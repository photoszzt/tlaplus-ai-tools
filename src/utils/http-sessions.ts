import { randomUUID } from "crypto";
import type { Express, Request, Response } from "express";
import type { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
import { isInitializeRequest } from "@modelcontextprotocol/sdk/types.js";

const MAX_SESSIONS = 32;
const IDLE_TIMEOUT_MS = 30 * 60 * 1000;

export function registerHttpSessionRoutes(
  app: Express,
  createServer: () => Promise<McpServer>,
  reportError: (error: unknown) => void,
): () => Promise<void> {
  const sessions = new Map<
    string,
    {
      server: McpServer;
      transport: StreamableHTTPServerTransport;
      lastActivity: number;
      activeRequests: number;
    }
  >();
  let pending = 0;
  const initializing = new Set<Promise<void>>();
  let closed = false;
  const fail = (res: Response, status: number, message: string) => {
    if (!res.headersSent)
      res.status(status).json({
        jsonrpc: "2.0",
        id: null,
        error: { code: -32000, message },
      });
  };
  const dispose = async (id: string) => {
    const session = sessions.get(id);
    sessions.delete(id);
    if (session) await session.server.close().catch(reportError);
  };
  const timer = setInterval(() => {
    const now = Date.now();
    for (const [id, session] of sessions) {
      if (session.activeRequests === 0 && now - session.lastActivity >= IDLE_TIMEOUT_MS) {
        void dispose(id);
      }
    }
  }, 60000);
  timer.unref();

  app.post("/mcp", async (req: Request, res: Response) => {
    const id = req.headers["mcp-session-id"];
    let server: McpServer | undefined;
    let registeredId: string | undefined;
    let initialization: Promise<void> | undefined;
    let finishInitialization: () => void = () => {};
    try {
      if (closed) return fail(res, 503, "Server is shutting down");
      if (id !== undefined) {
        const session = typeof id === "string" ? sessions.get(id) : undefined;
        if (!session) return fail(res, 404, "Unknown MCP session");
        session.lastActivity = Date.now();
        session.activeRequests++;
        res.once("close", () => {
          session.activeRequests--;
          session.lastActivity = Date.now();
        });
        await session.transport.handleRequest(req, res, req.body);
        return;
      }
      if (!isInitializeRequest(req.body)) return fail(res, 400, "Initialize an MCP session first");
      if (sessions.size + pending >= MAX_SESSIONS)
        return fail(res, 503, "MCP session limit reached");
      pending++;
      initialization = new Promise<void>((resolve) => {
        finishInitialization = resolve;
      });
      initializing.add(initialization);
      const initializedServer = await createServer();
      server = initializedServer;
      const transport = new StreamableHTTPServerTransport({
        sessionIdGenerator: randomUUID,
        onsessioninitialized: (sessionId) => {
          if (closed) throw new Error("Server is shutting down");
          registeredId = sessionId;
          sessions.set(sessionId, {
            server: initializedServer,
            transport,
            lastActivity: Date.now(),
            activeRequests: 0,
          });
        },
      });
      await server.connect(transport);
      const sdkClose = transport.onclose;
      transport.onclose = () => {
        sdkClose?.();
        if (transport.sessionId) sessions.delete(transport.sessionId);
      };
      if (closed) {
        await server.close();
        return fail(res, 503, "Server is shutting down");
      }
      await transport.handleRequest(req, res, req.body);
      if (!registeredId) await server.close();
    } catch (error) {
      reportError(error);
      if (registeredId) await dispose(registeredId);
      else await server?.close().catch(reportError);
      fail(res, 500, "Internal server error");
    } finally {
      if (initialization) {
        pending--;
        initializing.delete(initialization);
        finishInitialization();
      }
    }
  });
  for (const method of ["get", "delete"] as const) {
    app[method]("/mcp", async (req: Request, res: Response) => {
      const id = req.headers["mcp-session-id"];
      const session = typeof id === "string" ? sessions.get(id) : undefined;
      if (!session) return fail(res, 404, "Unknown MCP session");
      session.lastActivity = Date.now();
      try {
        await session.transport.handleRequest(req, res);
      } catch (error) {
        reportError(error);
        fail(res, 500, "Internal server error");
      }
    });
  }
  return async () => {
    closed = true;
    clearInterval(timer);
    await Promise.all([...sessions.keys()].map(dispose));
    await Promise.all(initializing);
  };
}
