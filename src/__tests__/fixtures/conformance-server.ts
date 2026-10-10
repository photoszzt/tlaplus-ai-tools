// Test-only fixtures for modelcontextprotocol/conformance@c37eec888e1c.
// Optional fixture capabilities are not part of the shipped plugin.
import express from "express";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { randomUUID } from "crypto";
import { z } from "zod";
import { ResourceTemplate, McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
import {
  CompleteRequestSchema,
  SubscribeRequestSchema,
  UnsubscribeRequestSchema,
  McpError,
  ErrorCode,
  type CallToolResult,
} from "@modelcontextprotocol/sdk/types.js";
import { TLAPlusMCPServer } from "../../server";
import { applyHttpSecurity } from "../../utils/http-security";
import { runTlcAndWait } from "../../utils/tlc-helpers";
import { reportTlcProgress, type ToolContext } from "../../tools/tlc";

const png =
  "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+jRZkAAAAASUVORK5CYII=";
const text = (value: string): CallToolResult => ({ content: [{ type: "text", text: value }] });
const image = { type: "image" as const, data: png, mimeType: "image/png" };
const resource = {
  type: "resource" as const,
  resource: {
    uri: "test://embedded",
    mimeType: "text/plain",
    text: "TLA+ fixture resource",
  },
};

async function registerFixtures(
  server: McpServer,
  owner: TLAPlusMCPServer,
  dir: string,
  toolsDir: string,
) {
  const fixtureTlc = async (context: ToolContext) => {
    const result = await runTlcAndWait(
      path.join(dir, "Counter.tla"),
      path.join(dir, "Counter.cfg"),
      [],
      [],
      toolsDir,
      undefined,
      10000,
      context.signal,
      (event, notificationSignal) =>
        reportTlcProgress(
          context,
          event,
          (level, message, extra) => owner.sendLog(level, message, extra),
          notificationSignal,
        ),
    );
    if (result.exitCode !== 0) throw new Error(`Fixture TLC failed: ${result.output.join("\n")}`);
    return text("TLC fixture completed");
  };
  server.registerTool(
    "test_simple_text",
    { description: "Conformance fixture test_simple_text" },
    async () => text("TLA+ text fixture"),
  );
  server.registerTool(
    "test_image_content",
    { description: "Conformance fixture test_image_content" },
    async () => ({ content: [image] }),
  );
  const wav = Buffer.alloc(46);
  wav.write("RIFF");
  wav.writeUInt32LE(38, 4);
  wav.write("WAVEfmt ", 8);
  wav.writeUInt32LE(16, 16);
  wav.writeUInt16LE(1, 20);
  wav.writeUInt16LE(1, 22);
  wav.writeUInt32LE(8000, 24);
  wav.writeUInt32LE(16000, 28);
  wav.writeUInt16LE(2, 32);
  wav.writeUInt16LE(16, 34);
  wav.write("data", 36);
  wav.writeUInt32LE(2, 40);
  server.registerTool(
    "test_audio_content",
    { description: "Conformance fixture test_audio_content" },
    async () => ({
      content: [{ type: "audio", mimeType: "audio/wav", data: wav.toString("base64") }],
    }),
  );
  server.registerTool(
    "test_embedded_resource",
    { description: "Conformance fixture test_embedded_resource" },
    async () => ({ content: [resource] }),
  );
  server.registerTool(
    "test_multiple_content_types",
    { description: "Conformance fixture test_multiple_content_types" },
    async () => ({ content: [{ type: "text", text: "Mixed fixture" }, image, resource] }),
  );
  server.registerTool(
    "test_error_handling",
    { description: "Conformance fixture test_error_handling" },
    async () => ({ ...text("Intentional fixture error"), isError: true }),
  );
  server.registerTool(
    "test_tool_with_progress",
    { description: "Conformance fixture test_tool_with_progress", inputSchema: {} },
    async (_args, extra) => fixtureTlc(extra),
  );
  server.registerTool(
    "test_tool_with_logging",
    { description: "Conformance fixture test_tool_with_logging", inputSchema: {} },
    async (_args, extra) => fixtureTlc(extra),
  );
  server.registerTool(
    "test_sampling",
    { description: "Conformance fixture test_sampling", inputSchema: { prompt: z.string() } },
    async ({ prompt }, extra) => {
      const result = await server.server.createMessage(
        {
          messages: [{ role: "user", content: { type: "text", text: prompt } }],
          maxTokens: 100,
        },
        { relatedRequestId: extra.requestId },
      );
      return text(JSON.stringify(result));
    },
  );
  server.registerTool(
    "test_elicitation",
    { description: "Conformance fixture test_elicitation", inputSchema: { message: z.string() } },
    async ({ message }, extra) => {
      const result = await server.server.elicitInput(
        {
          message,
          requestedSchema: {
            type: "object",
            properties: { username: { type: "string" }, email: { type: "string" } },
            required: ["username", "email"],
          },
        },
        { relatedRequestId: extra.requestId },
      );
      return text(JSON.stringify(result));
    },
  );
  server.registerTool(
    "test_elicitation_sep1034_defaults",
    { description: "Conformance fixture test_elicitation_sep1034_defaults", inputSchema: {} },
    async (_args, extra) => {
      const result = await server.server.elicitInput(
        {
          message: "Defaults fixture",
          requestedSchema: {
            type: "object",
            properties: {
              name: { type: "string", default: "John Doe" },
              age: { type: "integer", default: 30 },
              score: { type: "number", default: 95.5 },
              status: {
                type: "string",
                enum: ["active", "inactive", "pending"],
                default: "active",
              },
              verified: { type: "boolean", default: true },
            },
          },
        },
        { relatedRequestId: extra.requestId },
      );
      return text(JSON.stringify(result));
    },
  );
  server.registerTool(
    "test_elicitation_sep1330_enums",
    { description: "Conformance fixture test_elicitation_sep1330_enums", inputSchema: {} },
    async (_args, extra) => {
      const result = await server.server.elicitInput(
        {
          message: "Enums fixture",
          requestedSchema: {
            type: "object",
            properties: {
              untitledSingle: { type: "string", enum: ["option1", "option2", "option3"] },
              titledSingle: {
                type: "string",
                oneOf: [
                  { const: "value1", title: "First Option" },
                  { const: "value2", title: "Second Option" },
                ],
              },
              legacyEnum: {
                type: "string",
                enum: ["opt1", "opt2", "opt3"],
                enumNames: ["Option One", "Option Two", "Option Three"],
              },
              untitledMulti: {
                type: "array",
                items: { type: "string", enum: ["option1", "option2", "option3"] },
              },
              titledMulti: {
                type: "array",
                items: {
                  anyOf: [
                    { const: "value1", title: "First Choice" },
                    { const: "value2", title: "Second Choice" },
                  ],
                },
              },
            },
          },
        },
        { relatedRequestId: extra.requestId },
      );
      return text(JSON.stringify(result));
    },
  );
  server.registerResource(
    "static-text",
    "test://static-text",
    { mimeType: "text/plain" },
    async (uri) => ({
      contents: [{ uri: uri.href, mimeType: "text/plain", text: "Text fixture" }],
    }),
  );
  server.registerResource(
    "static-binary",
    "test://static-binary",
    { mimeType: "application/octet-stream" },
    async (uri) => ({
      contents: [
        {
          uri: uri.href,
          mimeType: "application/octet-stream",
          blob: Buffer.from("Binary fixture").toString("base64"),
        },
      ],
    }),
  );
  server.registerResource(
    "template",
    new ResourceTemplate("test://template/{id}/data", { list: undefined }),
    {},
    async (uri, variables) => ({ contents: [{ uri: uri.href, text: `Template ${variables.id}` }] }),
  );
  server.registerResource("watched", "test://watched-resource", {}, async (uri) => ({
    contents: [{ uri: uri.href, text: "Watched fixture" }],
  }));
  const subscriptions = new Set<string>();
  server.server.registerCapabilities({ resources: { subscribe: true } });
  server.server.setRequestHandler(SubscribeRequestSchema, async ({ params }) => {
    if (params.uri !== "test://watched-resource")
      throw new McpError(ErrorCode.InvalidParams, "Unknown fixture resource");
    subscriptions.add(params.uri);
    return {};
  });
  server.server.setRequestHandler(UnsubscribeRequestSchema, async ({ params }) => {
    subscriptions.delete(params.uri);
    return {};
  });
  server.registerPrompt(
    "test_simple_prompt",
    { description: "Conformance fixture test_simple_prompt" },
    async () => ({
      messages: [{ role: "user", content: { type: "text", text: "TLA+ fixture prompt" } }],
    }),
  );
  server.registerPrompt(
    "test_prompt_with_arguments",
    {
      description: "Conformance fixture test_prompt_with_arguments",
      argsSchema: { arg1: z.string(), arg2: z.string() },
    },
    async ({ arg1, arg2 }) => ({
      messages: [{ role: "user", content: { type: "text", text: `${arg1} ${arg2}` } }],
    }),
  );
  server.registerPrompt(
    "test_prompt_with_embedded_resource",
    {
      description: "Conformance fixture test_prompt_with_embedded_resource",
      argsSchema: { resourceUri: z.string() },
    },
    async ({ resourceUri }) => ({
      messages: [
        {
          role: "user",
          content: { type: "resource", resource: { ...resource.resource, uri: resourceUri } },
        },
      ],
    }),
  );
  server.registerPrompt(
    "test_prompt_with_image",
    { description: "Conformance fixture test_prompt_with_image" },
    async () => ({ messages: [{ role: "user", content: image }] }),
  );
  server.server.registerCapabilities({ completions: {} });
  server.server.setRequestHandler(CompleteRequestSchema, async () => ({
    completion: { values: [], total: 0, hasMore: false },
  }));
}

export async function startConformanceServer() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tlaplus-conformance-fixtures-"));
  const toolsDir = path.resolve("tools");
  if (!fs.existsSync(path.join(toolsDir, "tla2tools.jar")))
    throw new Error("Run npm run setup before conformance tests");
  fs.writeFileSync(
    path.join(dir, "Counter.tla"),
    "---- MODULE Counter ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\n====\n",
  );
  fs.writeFileSync(path.join(dir, "Counter.cfg"), "INIT Init\nNEXT Next\n");
  const owner = new TLAPlusMCPServer({
    http: true,
    port: 0,
    workingDir: dir,
    toolsDir,
    kbDir: path.resolve("resources/knowledgebase"),
    javaHome: null,
    verbose: false,
  });
  const sessions = new Map<
    string,
    { transport: StreamableHTTPServerTransport; server: McpServer }
  >();
  const app = express();
  applyHttpSecurity(app);
  app.use(express.json());
  app.post("/mcp", async (req, res) => {
    const id = req.headers["mcp-session-id"];
    if (typeof id === "string" && sessions.has(id)) {
      await sessions.get(id)!.transport.handleRequest(req, res, req.body);
      return;
    }
    if (id || req.body?.method !== "initialize") {
      res.status(id ? 404 : 400).json({
        jsonrpc: "2.0",
        id: null,
        error: { code: -32000, message: "Unknown fixture session" },
      });
      return;
    }
    const server = await owner.createMCPServer();
    await registerFixtures(server, owner, dir, toolsDir);
    const transport = new StreamableHTTPServerTransport({
      sessionIdGenerator: randomUUID,
      onsessioninitialized: (sessionId) => {
        sessions.set(sessionId, { transport, server });
      },
    });
    await server.connect(transport);
    const sdkClose = transport.onclose;
    transport.onclose = () => {
      sdkClose?.();
      if (transport.sessionId) sessions.delete(transport.sessionId);
    };
    await transport.handleRequest(req, res, req.body);
  });
  for (const method of ["get", "delete"] as const) {
    app[method]("/mcp", async (req, res) => {
      const id = req.headers["mcp-session-id"];
      const entry = typeof id === "string" ? sessions.get(id) : undefined;
      if (!entry) {
        res.status(404).json({
          jsonrpc: "2.0",
          id: null,
          error: { code: -32000, message: "Unknown fixture session" },
        });
        return;
      }
      await entry.transport.handleRequest(req, res);
    });
  }
  const listener = app.listen(0, "127.0.0.1");
  await new Promise<void>((resolve, reject) => {
    listener.once("listening", resolve);
    listener.once("error", reject);
  });
  const address = listener.address();
  if (!address || typeof address === "string") throw new Error("Fixture server has no TCP address");
  console.log(`Conformance fixture listening at http://127.0.0.1:${address.port}/mcp`);
  const close = async () => {
    await Promise.all([...sessions.values()].map(({ server }) => server.close()));
    listener.closeAllConnections();
    await new Promise<void>((resolve) => listener.close(() => resolve()));
    fs.rmSync(dir, { recursive: true, force: true });
  };
  return { port: address.port, close };
}

if (require.main === module) {
  startConformanceServer()
    .then(({ close }) => {
      for (const signal of ["SIGINT", "SIGTERM"] as const)
        process.once(signal, () => {
          void close();
        });
    })
    .catch((error) => {
      console.error(error);
      process.exitCode = 1;
    });
}
