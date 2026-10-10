import fs from "fs";
import * as os from "os";
import * as path from "path";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import {
  ResourceListChangedNotificationSchema,
  ResourceUpdatedNotificationSchema,
} from "@modelcontextprotocol/sdk/types.js";
import {
  KnowledgeCatalog,
  KNOWLEDGE_URI_TEMPLATE,
  registerKnowledgeBaseFromCache,
  registerKnowledgeTemplate,
} from "../tools/knowledge";

const articleUri = "tlaplus://knowledge/tla-alpha.md";
const article = (title: string, body: string) =>
  `---\ntitle: ${title}\ndescription: Description ${title}\n---\n${body}\n`;
const pause = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms));
async function until(predicate: () => boolean | Promise<boolean>) {
  const deadline = Date.now() + 3000;
  while (!(await predicate())) {
    if (Date.now() > deadline) throw new Error("Timed out waiting for catalog update");
    await pause(20);
  }
}

describe("KnowledgeCatalog with real SDK clients", () => {
  let dir: string;
  const connections: Array<{ client: Client; server: McpServer; dispose: () => void }> = [];

  beforeEach(async () => {
    dir = await fs.promises.mkdtemp(path.join(os.tmpdir(), "tla-knowledge-"));
    await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), article("Alpha", "# Original"));
    await fs.promises.writeFile(path.join(dir, "other.md"), "# Other");
  });
  afterEach(async () => {
    for (const connection of connections.splice(0)) {
      connection.dispose();
      await connection.client.close();
      await connection.server.close();
    }
    await fs.promises.rm(dir, { recursive: true, force: true });
  });

  async function connect(catalog: KnowledgeCatalog, onClose?: () => void) {
    await catalog.refresh();
    const server = new McpServer({ name: "knowledge-test", version: "1.0.0" });
    server.server.onclose = onClose;
    const dispose = catalog.register(server);
    const client = new Client({ name: "knowledge-client", version: "1.0.0" });
    const updates: string[] = [];
    let listChanges = 0;
    client.setNotificationHandler(ResourceUpdatedNotificationSchema, async ({ params }) => {
      expect(Object.keys(params)).toEqual(["uri"]);
      updates.push(params.uri);
    });
    client.setNotificationHandler(ResourceListChangedNotificationSchema, async () => {
      listChanges++;
    });
    const [clientTransport, serverTransport] = InMemoryTransport.createLinkedPair();
    await server.connect(serverTransport);
    await client.connect(clientTransport);
    const connection = { client, server, dispose, updates, listChanges: () => listChanges };
    connections.push(connection);
    return connection;
  }

  it("lists static articles and a template, reads stripped content and completes article prefixes", async () => {
    const catalog = await KnowledgeCatalog.fromDirectory(dir);
    const { client } = await connect(catalog);
    expect(client.getServerCapabilities()?.resources).toMatchObject({
      subscribe: true,
      listChanged: true,
    });
    expect((await client.listResources()).resources).toHaveLength(2);
    expect((await client.listResourceTemplates()).resourceTemplates).toEqual([
      expect.objectContaining({ uriTemplate: KNOWLEDGE_URI_TEMPLATE, mimeType: "text/markdown" }),
    ]);
    expect((await client.readResource({ uri: articleUri })).contents[0]).toMatchObject({
      text: "# Original\n",
    });
    const result = await client.complete({
      ref: { type: "ref/resource", uri: KNOWLEDGE_URI_TEMPLATE },
      argument: { name: "article", value: "tla-" },
    });
    expect(result.completion.values).toEqual(["tla-alpha.md"]);
    for (const uri of [
      "tlaplus://knowledge/missing.md",
      "tlaplus://knowledge/../secret.md",
      "tlaplus://knowledge/%2Fetc%2Fpasswd",
      "tlaplus://knowledge/tla-alpha.md?query=1",
      "file:///etc/passwd",
    ]) {
      await expect(client.readResource({ uri })).rejects.toThrow();
      await expect(client.subscribeResource({ uri })).rejects.toThrow();
      await expect(client.unsubscribeResource({ uri })).rejects.toThrow();
    }
  });

  it("notifies only subscribed clients after real changes and updates cached content and metadata", async () => {
    const catalog = await KnowledgeCatalog.fromDirectory(dir);
    const first = await connect(catalog);
    const second = await connect(catalog);
    await first.client.subscribeResource({ uri: articleUri });
    await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), article("Updated", "# Changed"));
    await until(() => first.updates.length === 1);
    expect(second.updates).toEqual([]);
    expect((await second.client.readResource({ uri: articleUri })).contents[0]).toMatchObject({
      text: "# Changed\n",
    });
    expect(
      (await first.client.listResources()).resources.find((entry) => entry.uri === articleUri),
    ).toMatchObject({ title: "Updated", description: "Description Updated" });
    await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), article("Updated", "# Changed"));
    await pause(180);
    expect(first.updates).toEqual([articleUri]);
    await first.client.unsubscribeResource({ uri: articleUri });
    await second.client.subscribeResource({ uri: articleUri });
    await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), article("Final", "# Final"));
    await until(() => second.updates.length === 1);
    expect(first.updates).toEqual([articleUri]);
  });

  it("updates lists and completion when articles are added or deleted, then rejects deleted reads", async () => {
    const { client, updates, listChanges } = await connect(
      await KnowledgeCatalog.fromDirectory(dir),
    );
    await client.subscribeResource({ uri: articleUri });
    await fs.promises.writeFile(path.join(dir, "tla-beta.md"), "# Beta");
    await until(async () => (await client.listResources()).resources.length === 3);
    const result = await client.complete({
      ref: { type: "ref/resource", uri: KNOWLEDGE_URI_TEMPLATE },
      argument: { name: "article", value: "tla-" },
    });
    expect(result.completion.values).toEqual(["tla-alpha.md", "tla-beta.md"]);
    await fs.promises.unlink(path.join(dir, "tla-alpha.md"));
    await until(() => updates.length === 1);
    expect((await client.listResources()).resources.map((entry) => entry.uri)).not.toContain(
      articleUri,
    );
    await expect(client.readResource({ uri: articleUri })).rejects.toThrow();
    await expect(client.unsubscribeResource({ uri: articleUri })).resolves.toEqual({});
    await expect(client.unsubscribeResource({ uri: articleUri })).resolves.toEqual({});
    expect(listChanges()).toBeGreaterThanOrEqual(2);
  });

  it("shares one watcher, chains transport close, and closes after the last registration", async () => {
    const watch = jest.spyOn(fs, "watch");
    try {
      const catalog = await KnowledgeCatalog.fromDirectory(dir);
      const firstClosed = jest.fn();
      const first = await connect(catalog, firstClosed);
      const second = await connect(catalog);
      expect(watch).toHaveBeenCalledTimes(1);
      const watcher = watch.mock.results[0].value;
      const closed = jest.fn();
      watcher.on("close", closed);
      await first.client.close();
      await pause(40);
      expect(firstClosed).toHaveBeenCalledTimes(1);
      expect(closed).not.toHaveBeenCalled();
      second.dispose();
      second.dispose();
      await until(() => closed.mock.calls.length === 1);
      expect((await second.client.listResources()).resources).toEqual([]);
      await fs.promises.writeFile(path.join(dir, "fresh.md"), "# Fresh");
      const third = await connect(catalog);
      expect(watch).toHaveBeenCalledTimes(2);
      expect(
        (await third.client.listResources()).resources.some((entry) => entry.name === "fresh.md"),
      ).toBe(true);
    } finally {
      watch.mockRestore();
    }
  });

  it("ignores unsafe filenames and retains the cache after read failures", async () => {
    const errors = jest.spyOn(console, "error").mockImplementation(() => {});
    try {
      await fs.promises.writeFile(path.join(dir, "unsafe name.md"), "# Ignored");
      const { client, updates } = await connect(await KnowledgeCatalog.fromDirectory(dir));
      expect((await client.listResources()).resources).toHaveLength(2);
      await client.subscribeResource({ uri: articleUri });
      await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), Buffer.alloc(1024 * 1024 + 1));
      await until(() => errors.mock.calls.some((call) => String(call[1]).includes("too large")));
      expect((await client.readResource({ uri: articleUri })).contents[0]).toMatchObject({
        text: "# Original\n",
      });
      expect(updates).toEqual([]);
    } finally {
      errors.mockRestore();
    }
  });

  it("does not expose a symlink escaping the knowledge directory", async () => {
    const outside = await fs.promises.mkdtemp(path.join(os.tmpdir(), "tla-knowledge-outside-"));
    try {
      const secret = path.join(outside, "secret.md");
      await fs.promises.writeFile(secret, "Private content outside the knowledge base");
      try {
        await fs.promises.symlink(secret, path.join(dir, "escape.md"));
      } catch (error) {
        if (
          process.platform === "win32" &&
          error instanceof Error &&
          "code" in error &&
          (error.code === "EPERM" || error.code === "EACCES")
        )
          return;
        throw error;
      }
      const { client } = await connect(await KnowledgeCatalog.fromDirectory(dir));
      expect((await client.listResources()).resources.map((entry) => entry.name)).not.toContain(
        "escape.md",
      );
      await expect(client.readResource({ uri: "tlaplus://knowledge/escape.md" })).rejects.toThrow();
      await expect(
        client.subscribeResource({ uri: "tlaplus://knowledge/escape.md" }),
      ).rejects.toThrow();
    } finally {
      await fs.promises.rm(outside, { recursive: true, force: true });
    }
  });

  it("registers an immutable template without creating a watcher or advertising subscriptions", async () => {
    const watch = jest.spyOn(fs, "watch");
    const server = new McpServer({ name: "static-knowledge", version: "1.0.0" });
    const client = new Client({ name: "static-client", version: "1.0.0" });
    try {
      const catalog = await KnowledgeCatalog.fromDirectory(dir);
      const entries = catalog.entries;
      await registerKnowledgeBaseFromCache(server, entries);
      registerKnowledgeTemplate(server, entries);
      const [clientTransport, serverTransport] = InMemoryTransport.createLinkedPair();
      await server.connect(serverTransport);
      await client.connect(clientTransport);
      await fs.promises.writeFile(path.join(dir, "tla-alpha.md"), "# New disk content");
      expect((await client.readResource({ uri: articleUri })).contents[0]).toMatchObject({
        text: "# Original\n",
      });
      expect(client.getServerCapabilities()?.resources?.subscribe).toBeUndefined();
      expect(watch).not.toHaveBeenCalled();
    } finally {
      await client.close();
      await server.close();
      watch.mockRestore();
    }
  });
});
