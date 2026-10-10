import * as fs from "fs";
import * as path from "path";
import { McpServer, type RegisteredResource } from "@modelcontextprotocol/sdk/server/mcp.js";
import {
  ErrorCode,
  McpError,
  SubscribeRequestSchema,
  UnsubscribeRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { parseMarkdownFrontmatter } from "../utils/markdown";
import {
  knowledgeResourceContent,
  registerKnowledgeTemplate,
  type KnowledgeBaseEntry,
} from "./knowledge";

const MAX_ARTICLES = 1024;
const MAX_ARTICLE_BYTES = 1024 * 1024;
const DEBOUNCE_MS = 40;
const articleName = /^[A-Za-z0-9][A-Za-z0-9._-]*\.md$/;

type Registration = {
  server: McpServer;
  resources: Map<string, RegisteredResource>;
  subscriptions: Set<string>;
  knownSubscriptions: Set<string>;
};

/** A single watched snapshot shared by persistent MCP sessions. */
export class KnowledgeCatalog {
  private articles = new Map<string, KnowledgeBaseEntry>();
  private registrations = new Set<Registration>();
  private watcher?: fs.FSWatcher;
  private timer?: NodeJS.Timeout;
  private refreshes = Promise.resolve();

  private constructor(private readonly kbDir: string) {}

  static async fromDirectory(kbDir: string): Promise<KnowledgeCatalog> {
    const catalog = new KnowledgeCatalog(await fs.promises.realpath(kbDir));
    catalog.articles = await catalog.readDirectory();
    return catalog;
  }

  get entries(): KnowledgeBaseEntry[] {
    return [...this.articles.values()].map((entry) => ({ ...entry }));
  }

  /** Refresh before attaching a session, including when the watcher was stopped. */
  refresh(): Promise<void> {
    this.refreshes = this.refreshes
      .then(() => this.reload())
      .catch((error) => this.reportError(error));
    return this.refreshes;
  }

  register(server: McpServer): () => void {
    const registration: Registration = {
      server,
      resources: new Map(),
      subscriptions: new Set(),
      knownSubscriptions: new Set(),
    };
    for (const entry of this.articles.values()) this.addResource(registration, entry);
    const template = registerKnowledgeTemplate(server, () => this.entries);
    server.server.registerCapabilities({ resources: { subscribe: true, listChanged: true } });
    server.server.setRequestHandler(SubscribeRequestSchema, async ({ params }) => {
      this.requireArticle(params.uri);
      if (
        !registration.knownSubscriptions.has(params.uri) &&
        registration.knownSubscriptions.size >= MAX_ARTICLES
      ) {
        throw new McpError(ErrorCode.InvalidParams, "Knowledge subscription limit reached");
      }
      registration.knownSubscriptions.add(params.uri);
      registration.subscriptions.add(params.uri);
      return {};
    });
    server.server.setRequestHandler(UnsubscribeRequestSchema, async ({ params }) => {
      if (!registration.knownSubscriptions.has(params.uri)) this.requireArticle(params.uri);
      registration.subscriptions.delete(params.uri);
      return {};
    });
    this.registrations.add(registration);
    if (!this.watcher) {
      try {
        this.watcher = fs.watch(this.kbDir, () => this.scheduleRefresh());
        this.watcher.on("error", (error) => this.reportError(error));
        this.scheduleRefresh();
      } catch (error) {
        this.reportError(error);
      }
    }
    const previousOnClose = server.server.onclose;
    const dispose = () => {
      if (!this.registrations.delete(registration)) return;
      registration.subscriptions.clear();
      registration.knownSubscriptions.clear();
      for (const resource of registration.resources.values()) resource.remove();
      template.remove();
      server.server.removeRequestHandler("resources/subscribe");
      server.server.removeRequestHandler("resources/unsubscribe");
      if (server.server.onclose === onClose) server.server.onclose = previousOnClose;
      if (!this.registrations.size) {
        this.watcher?.close();
        this.watcher = undefined;
        if (this.timer) clearTimeout(this.timer);
        this.timer = undefined;
      }
    };
    const onClose = () => {
      dispose();
      previousOnClose?.();
    };
    server.server.onclose = onClose;
    return dispose;
  }

  private requireArticle(uri: string): KnowledgeBaseEntry {
    const entry = this.articles.get(uri);
    if (!entry) throw new McpError(ErrorCode.InvalidParams, "Unknown knowledge article");
    return entry;
  }

  private addResource(registration: Registration, entry: KnowledgeBaseEntry) {
    registration.resources.set(
      entry.resourceUri,
      registration.server.registerResource(
        entry.fileName,
        entry.resourceUri,
        { title: entry.title, description: entry.description, mimeType: "text/markdown" },
        async (uri) => knowledgeResourceContent(this.requireArticle(uri.href)),
      ),
    );
  }

  private async readDirectory(): Promise<Map<string, KnowledgeBaseEntry>> {
    const files = (await fs.promises.readdir(this.kbDir))
      .filter((file) => file.endsWith(".md") && articleName.test(file))
      .sort();
    if (files.length > MAX_ARTICLES)
      throw new Error(`Knowledge catalog exceeds ${MAX_ARTICLES} articles`);
    const entries = new Map<string, KnowledgeBaseEntry>();
    for (const fileName of files) {
      const resourceUri = `tlaplus://knowledge/${fileName}`;
      try {
        const filePath = path.join(this.kbDir, fileName);
        if (!(await fs.promises.lstat(filePath)).isFile()) continue;
        const realPath = await fs.promises.realpath(filePath);
        if (path.dirname(realPath) !== this.kbDir)
          throw new Error(`Knowledge article outside directory: ${fileName}`);
        const file = await fs.promises.open(
          realPath,
          fs.constants.O_RDONLY | (fs.constants.O_NOFOLLOW || 0) | (fs.constants.O_NONBLOCK || 0),
        );
        try {
          const stat = await file.stat();
          if (!stat.isFile()) continue;
          if (stat.size > MAX_ARTICLE_BYTES)
            throw new Error(`Knowledge article too large: ${fileName}`);
          const buffer = Buffer.alloc(MAX_ARTICLE_BYTES + 1);
          let size = 0;
          while (size < buffer.length) {
            const { bytesRead } = await file.read(buffer, size, buffer.length - size, null);
            if (!bytesRead) break;
            size += bytesRead;
          }
          if (size > MAX_ARTICLE_BYTES) throw new Error(`Knowledge article too large: ${fileName}`);
          const content = buffer.subarray(0, size).toString("utf8");
          const metadata = parseMarkdownFrontmatter(content);
          entries.set(resourceUri, {
            fileName,
            resourceUri,
            content,
            title: metadata.title || fileName,
            description: metadata.description || `TLA+ knowledge base article: ${fileName}`,
          });
        } finally {
          await file.close();
        }
      } catch (error) {
        this.reportError(error);
        const previous = this.articles.get(resourceUri);
        if (previous) entries.set(resourceUri, previous);
      }
    }
    return entries;
  }

  private scheduleRefresh() {
    if (this.timer) clearTimeout(this.timer);
    this.timer = setTimeout(() => {
      this.timer = undefined;
      void this.refresh();
    }, DEBOUNCE_MS);
    this.timer.unref();
  }

  private async reload() {
    const next = await this.readDirectory();
    const previous = this.articles;
    this.articles = next;
    for (const registration of this.registrations) {
      for (const [uri, oldEntry] of previous) {
        const entry = next.get(uri);
        if (!entry) {
          registration.resources.get(uri)?.remove();
          registration.resources.delete(uri);
          if (registration.subscriptions.has(uri)) this.notifyUpdated(registration, uri);
        } else if (entry.content !== oldEntry.content) {
          if (entry.title !== oldEntry.title || entry.description !== oldEntry.description) {
            registration.resources.get(uri)?.update({
              metadata: {
                title: entry.title,
                description: entry.description,
                mimeType: "text/markdown",
              },
            });
          }
          if (registration.subscriptions.has(uri)) this.notifyUpdated(registration, uri);
        }
      }
      for (const [uri, entry] of next) {
        if (!previous.has(uri)) {
          this.addResource(registration, entry);
          if (registration.subscriptions.has(uri)) this.notifyUpdated(registration, uri);
        }
      }
    }
  }

  private notifyUpdated(registration: Registration, uri: string) {
    if (!this.registrations.has(registration) || !registration.subscriptions.has(uri)) return;
    void registration.server.server
      .sendResourceUpdated({ uri })
      .catch((error) => this.reportError(error));
  }

  private reportError(error: unknown) {
    console.error(
      "[ERROR] Knowledge catalog:",
      error instanceof Error ? error.message : String(error),
    );
  }
}
