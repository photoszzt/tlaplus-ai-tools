import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import * as http from "http";
import express from "express";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StreamableHTTPClientTransport } from "@modelcontextprotocol/sdk/client/streamableHttp.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import {
  CallToolResultSchema,
  ElicitRequestSchema,
  CreateMessageRequestSchema,
  ResourceUpdatedNotificationSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { TLAPlusMCPServer } from "../../server";
import { registerHttpSessionRoutes } from "../../utils/http-sessions";
import { applyHttpSecurity } from "../../utils/http-security";
import { MINIMAL_CONFIG } from "../fixtures/config-samples";
import { parseArgs } from "../../cli";

describe("Persistent HTTP sessions through real MCP clients", () => {
  let dir: string;
  let listener: http.Server;
  let endpoint: URL;
  let closeSessions: () => Promise<void>;
  let clients: Client[];
  let errors: unknown[];
  let createServer: () => Promise<McpServer>;
  let expireSessions: () => void;

  beforeEach(async () => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), "mcp-sessions-"));
    fs.writeFileSync(path.join(dir, "article.md"), "# Original\n");
    clients = [];
    errors = [];
    const owner = new TLAPlusMCPServer({
      ...MINIMAL_CONFIG,
      http: true,
      httpSession: true,
      kbDir: dir,
      workingDir: dir,
      toolsDir: null,
    });
    const app = express();
    applyHttpSecurity(app);
    app.use(express.json());
    createServer = () => owner.createMCPServer(true);
    const nativeInterval = global.setInterval;
    const interval = jest
      .spyOn(global, "setInterval")
      .mockImplementation((callback, delay, ...args) => {
        if (delay === 60000) expireSessions = () => callback(...args);
        return nativeInterval(callback, delay, ...args);
      });
    try {
      closeSessions = registerHttpSessionRoutes(
        app,
        () => createServer(),
        (error) => errors.push(error),
      );
    } finally {
      interval.mockRestore();
    }
    listener = app.listen(0, "127.0.0.1");
    await new Promise<void>((resolve) => listener.once("listening", resolve));
    const address = listener.address();
    if (!address || typeof address === "string") throw new Error("No HTTP listener");
    endpoint = new URL(`http://127.0.0.1:${address.port}/mcp`);
  });

  afterEach(async () => {
    await Promise.all(clients.map((client) => client.close()));
    await closeSessions();
    listener.closeAllConnections();
    await new Promise<void>((resolve) => listener.close(() => resolve()));
    fs.rmSync(dir, { recursive: true, force: true });
  });

  async function connect(interactive = false, disableGet = false) {
    const client = new Client(
      { name: "http-session-test", version: "1" },
      {
        capabilities: interactive
          ? {
              sampling: {},
              elicitation: { form: {} },
            }
          : {},
      },
    );
    const transport = new StreamableHTTPClientTransport(
      endpoint,
      disableGet
        ? {
            fetch: async (url, init) =>
              init?.method === "GET" ? new Response(null, { status: 405 }) : fetch(url, init),
          }
        : undefined,
    );
    clients.push(client);
    await client.connect(transport);
    return { client, transport };
  }

  it("preserves default stateless mode and requires --http for the session flag", () => {
    expect(parseArgs(["--http"]).httpSession).toBeUndefined();
    expect(parseArgs(["--http", "--http-session"]).httpSession).toBe(true);
    expect(() => parseArgs(["--http-session"])).toThrow("requires --http");
  });

  it("keeps initialization alive across POSTs and deletes only the requested session", async () => {
    const a = await connect();
    const b = await connect();
    expect(a.transport.sessionId).toBeTruthy();
    expect(a.transport.sessionId).not.toBe(b.transport.sessionId);
    expect(a.client.getServerCapabilities()?.resources?.subscribe).toBe(true);
    expect(
      (await a.client.listPrompts()).prompts.some((prompt) => prompt.name === "tla-check"),
    ).toBe(true);
    await a.transport.terminateSession();
    const missing = await fetch(endpoint, {
      method: "GET",
      headers: {
        Accept: "text/event-stream",
        "mcp-session-id": "deleted-session",
      },
    });
    expect(missing.status).toBe(404);
    expect(
      (await b.client.readResource({ uri: "tlaplus://knowledge/article.md" })).contents[0],
    ).toMatchObject({ text: "# Original\n" });
    expect(errors).toHaveLength(0);
  });

  it("delivers subscription changes through GET SSE only to the subscribing client", async () => {
    const a = await connect();
    const b = await connect();
    const otherUpdates: string[] = [];
    b.client.setNotificationHandler(ResourceUpdatedNotificationSchema, ({ params }) => {
      otherUpdates.push(params.uri);
    });
    const updated = new Promise<string>((resolve) => {
      a.client.setNotificationHandler(ResourceUpdatedNotificationSchema, ({ params }) =>
        resolve(params.uri),
      );
    });
    await a.client.subscribeResource({ uri: "tlaplus://knowledge/article.md" });
    fs.writeFileSync(path.join(dir, "article.md"), "# Changed\n");
    expect(await updated).toBe("tlaplus://knowledge/article.md");
    expect(otherUpdates).toEqual([]);
    expect(
      (await b.client.readResource({ uri: "tlaplus://knowledge/article.md" })).contents[0],
    ).toMatchObject({ text: "# Changed\n" });
    await a.client.unsubscribeResource({ uri: "tlaplus://knowledge/article.md" });
    await expect(
      b.client.subscribeResource({ uri: "tlaplus://knowledge/..%2Fprivate.md" }),
    ).rejects.toThrow();
  });

  it("routes tool-triggered elicitation and sampling on the POST without a GET stream", async () => {
    const { client } = await connect(true, true);
    client.setRequestHandler(ElicitRequestSchema, async () => ({
      action: "accept",
      content: { mode: "check" },
    }));
    client.setRequestHandler(CreateMessageRequestSchema, async ({ params }) => {
      expect(params.includeContext).toBe("none");
      expect(params.messages[0].content).toEqual({ type: "text", text: "explicit-text" });
      return { role: "assistant", content: { type: "text", text: "Draft advice" }, model: "test" };
    });
    const result = CallToolResultSchema.parse(
      await client.callTool(
        {
          name: "tlaplus_mcp_tlc_prepare_config",
          arguments: {
            askUser: true,
            useSampling: true,
            specText: "explicit-text",
          },
        },
        undefined,
        { timeout: 3000 },
      ),
    );
    expect(result.isError).not.toBe(true);
    expect(JSON.stringify(result)).toContain("Draft advice");
  });

  it("drains pending initialization and closes its resources before shutdown returns", async () => {
    const factory = createServer;
    let begin: () => void = () => {};
    const started = new Promise<void>((resolve) => {
      begin = resolve;
    });
    let release: () => void = () => {};
    const gate = new Promise<void>((resolve) => {
      release = resolve;
    });
    let disposed = 0;
    createServer = async () => {
      begin();
      await gate;
      const server = await factory();
      const close = server.server.onclose;
      server.server.onclose = () => {
        disposed++;
        close?.();
      };
      return server;
    };
    const response = fetch(endpoint, {
      method: "POST",
      headers: {
        Accept: "application/json, text/event-stream",
        "Content-Type": "application/json",
      },
      body: JSON.stringify({
        jsonrpc: "2.0",
        id: 1,
        method: "initialize",
        params: {
          protocolVersion: "2025-11-25",
          capabilities: {},
          clientInfo: { name: "pending-test", version: "1" },
        },
      }),
    });
    await started;
    let finished = false;
    const closing = closeSessions().then(() => {
      finished = true;
    });
    await new Promise<void>((resolve) => setImmediate(resolve));
    expect(finished).toBe(false);
    release();
    await closing;
    expect((await response).status).toBe(503);
    expect(disposed).toBe(1);
  });

  it("disposes a prepared production server that never connects to a transport", async () => {
    const server = await createServer();
    let disposed = 0;
    const onClose = server.server.onclose;
    server.server.onclose = () => {
      disposed++;
      onClose?.();
    };
    await server.close();
    expect(disposed).toBe(1);
  });

  it("expires idle sessions while preserving an active tool request", async () => {
    const { client, transport } = await connect(true);
    let begin: () => void = () => {};
    const asked = new Promise<void>((resolve) => {
      begin = resolve;
    });
    let answer: () => void = () => {};
    client.setRequestHandler(ElicitRequestSchema, async () => {
      begin();
      return new Promise((resolve) => {
        answer = () => resolve({ action: "decline" });
      });
    });
    const draft = client.callTool({
      name: "tlaplus_mcp_tlc_prepare_config",
      arguments: { askUser: true },
    });
    await asked;
    const now = Date.now();
    const clock = jest.spyOn(Date, "now").mockReturnValue(now + 60 * 60 * 1000);
    try {
      expireSessions();
      expect((await client.listPrompts()).prompts.length).toBeGreaterThan(0);
      answer();
      await draft;
      clock.mockReturnValue(now + 2 * 60 * 60 * 1000);
      expireSessions();
      const expired = await fetch(endpoint, {
        method: "GET",
        headers: {
          Accept: "text/event-stream",
          "mcp-session-id": transport.sessionId ?? "missing",
        },
      });
      expect(expired.status).toBe(404);
    } finally {
      clock.mockRestore();
      answer();
    }
  });

  it("bounds session creation and frees capacity when a session is deleted", async () => {
    await closeSessions();
    listener.closeAllConnections();
    await new Promise<void>((resolve) => listener.close(() => resolve()));
    const app = express();
    app.use(express.json());
    closeSessions = registerHttpSessionRoutes(
      app,
      async () => new McpServer({ name: "capacity-test", version: "1" }),
      (error) => errors.push(error),
    );
    listener = app.listen(0, "127.0.0.1");
    await new Promise<void>((resolve) => listener.once("listening", resolve));
    const address = listener.address();
    if (!address || typeof address === "string") throw new Error("No HTTP listener");
    endpoint = new URL(`http://127.0.0.1:${address.port}/mcp`);
    const accepted = await Promise.all(Array.from({ length: 32 }, () => connect()));
    await expect(connect()).rejects.toThrow("MCP session limit reached");
    await accepted[0].transport.terminateSession();
    expect((await connect()).transport.sessionId).toBeTruthy();
  }, 20000);
});
