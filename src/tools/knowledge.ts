import * as fs from "fs";
import * as path from "path";
import { McpServer, ResourceTemplate } from "@modelcontextprotocol/sdk/server/mcp.js";
import { ErrorCode, McpError } from "@modelcontextprotocol/sdk/types.js";
import { parseMarkdownFrontmatter, removeMarkdownFrontmatter } from "../utils/markdown";

export { KnowledgeCatalog } from "./knowledge-catalog";

export const KNOWLEDGE_URI_TEMPLATE = "tlaplus://knowledge/{article}";

/**
 * Cached knowledge base entry for HTTP mode pre-loading.
 *
 * @implements REQ-REVIEW-005, SCN-REVIEW-005-01
 */
export interface KnowledgeBaseEntry {
  fileName: string;
  resourceUri: string;
  title: string;
  description: string;
  content: string;
}

export function knowledgeResourceContent(entry: KnowledgeBaseEntry) {
  return {
    contents: [
      {
        uri: entry.resourceUri,
        mimeType: "text/markdown",
        text: removeMarkdownFrontmatter(entry.content),
      },
    ],
  };
}

/** Register a template against either an immutable cache or a live catalog snapshot. */
export function registerKnowledgeTemplate(
  server: McpServer,
  entries: KnowledgeBaseEntry[] | (() => KnowledgeBaseEntry[]),
) {
  const snapshot = typeof entries === "function" ? entries : () => entries;
  return server.registerResource(
    "knowledge-article",
    new ResourceTemplate(KNOWLEDGE_URI_TEMPLATE, {
      list: undefined,
      complete: {
        article: async (prefix) =>
          snapshot()
            .map((entry) => entry.fileName)
            .filter((fileName) => fileName.startsWith(prefix))
            .sort(),
      },
    }),
    { title: "TLA+ knowledge article", mimeType: "text/markdown" },
    async (uri) => {
      const entry = snapshot().find((candidate) => candidate.resourceUri === uri.href);
      if (!entry) throw new McpError(ErrorCode.InvalidParams, "Unknown knowledge article");
      return knowledgeResourceContent(entry);
    },
  );
}

/**
 * Register all knowledge base articles as MCP resources
 * Reads all .md files from the knowledge base directory and registers them
 *
 * @param server MCP server instance
 * @param kbDir Path to knowledge base directory
 */
export async function registerKnowledgeBaseResources(
  server: McpServer,
  kbDir: string,
): Promise<void> {
  try {
    // Read all files from the knowledge base directory
    const files = await fs.promises.readdir(kbDir);

    // Filter for .md files only
    const markdownFiles = files.filter((file) => file.endsWith(".md"));

    // Register each markdown file as a resource
    for (const fileName of markdownFiles) {
      const filePath = path.join(kbDir, fileName);

      // Read file content to extract metadata
      const content = await fs.promises.readFile(filePath, "utf-8");
      const metadata = parseMarkdownFrontmatter(content);

      // Generate resource URI
      const resourceUri = `tlaplus://knowledge/${fileName}`;

      // Register the resource
      server.resource(
        fileName,
        resourceUri,
        {
          title: metadata.title || fileName,
          description: metadata.description || `TLA+ knowledge base article: ${fileName}`,
          mimeType: "text/markdown",
        },
        async () => {
          // Handler: Read file and return content without frontmatter
          const fullContent = await fs.promises.readFile(filePath, "utf-8");
          const contentWithoutFrontmatter = removeMarkdownFrontmatter(fullContent);

          return {
            contents: [
              {
                uri: resourceUri,
                mimeType: "text/markdown",
                text: contentWithoutFrontmatter,
              },
            ],
          };
        },
      );
    }

    console.error(`[INFO] Registered ${markdownFiles.length} knowledge base articles`);
  } catch (error) {
    console.error(
      `[ERROR] Failed to register knowledge base resources: ${error instanceof Error ? error.message : String(error)}`,
    );
  }
}

/**
 * Register knowledge base resources from pre-loaded cached content (no disk I/O).
 * Used in HTTP mode where KB is pre-loaded at startup.
 *
 * @implements REQ-REVIEW-005, SCN-REVIEW-005-01, SCN-REVIEW-005-02
 * @param server MCP server instance
 * @param entries Pre-loaded knowledge base entries
 */
export async function registerKnowledgeBaseFromCache(
  server: McpServer,
  entries: KnowledgeBaseEntry[],
): Promise<void> {
  for (const entry of entries) {
    server.resource(
      entry.fileName,
      entry.resourceUri,
      {
        title: entry.title,
        description: entry.description,
        mimeType: "text/markdown",
      },
      async () => {
        // Use cached content -- no disk I/O
        const contentWithoutFrontmatter = removeMarkdownFrontmatter(entry.content);
        return {
          contents: [
            {
              uri: entry.resourceUri,
              mimeType: "text/markdown",
              text: contentWithoutFrontmatter,
            },
          ],
        };
      },
    );
  }
  console.debug(`[DEBUG] Registered ${entries.length} knowledge base articles (from cache)`);
}
