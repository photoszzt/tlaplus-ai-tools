import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import { registerKnowledgeBaseResources, registerKnowledgeBaseFromCache } from "../knowledge";

describe.each(["disk", "cache"])("Knowledge resource protocol: %s", (mode) => {
  it("lists a valid URI and reads the article using that URI", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "knowledge-protocol-"));
    const fileName = "article.md";
    const resourceUri = `tlaplus://knowledge/${fileName}`;
    const content = "---\ntitle: Test article\n---\n# Knowledge\nArticle content\n";
    fs.writeFileSync(path.join(dir, fileName), content);
    const server = new McpServer({ name: "knowledge-test", version: "1.0" });
    const client = new Client({ name: "knowledge-client", version: "1.0" });
    try {
      if (mode === "disk") {
        await registerKnowledgeBaseResources(server, dir);
      } else {
        await registerKnowledgeBaseFromCache(server, [
          {
            fileName,
            resourceUri,
            title: "Test article",
            description: "Test",
            content,
          },
        ]);
      }
      const [clientTransport, serverTransport] = InMemoryTransport.createLinkedPair();
      await server.connect(serverTransport);
      await client.connect(clientTransport);
      const listed = await client.listResources();
      expect(listed.resources).toHaveLength(1);
      expect(listed.resources[0].uri).toBe(resourceUri);
      expect(listed.resources[0].name).toBe(fileName);
      expect(new URL(listed.resources[0].uri).href).toBe(resourceUri);
      const result = await client.readResource({ uri: listed.resources[0].uri });
      expect(result.contents).toEqual([
        { uri: resourceUri, mimeType: "text/markdown", text: "# Knowledge\nArticle content\n" },
      ]);
    } finally {
      await client.close();
      await server.close();
      fs.rmSync(dir, { recursive: true, force: true });
    }
  });
});
