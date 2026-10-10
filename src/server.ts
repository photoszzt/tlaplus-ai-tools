import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
import { applyHttpSecurity } from "./utils/http-security";
import express from "express";
import * as fs from "fs";
import * as http from "http";
import * as path from "path";
import { ServerConfig } from "./types";
import { Logger } from "./utils/logging";
import { parseMarkdownFrontmatter } from "./utils/markdown";
import { registerSanyTools } from "./tools/sany";
import { registerTlcTools, ToolContext } from "./tools/tlc";
import {
  LoggingLevelSchema,
  SetLevelRequestSchema,
  type LoggingLevel,
} from "@modelcontextprotocol/sdk/types.js";
import {
  registerKnowledgeBaseResources,
  registerKnowledgeBaseFromCache,
  KnowledgeBaseEntry,
} from "./tools/knowledge";
import { registerAnimationTools } from "./tools/animation";
import { registerWorkflowPrompts } from "./tools/workflows";
import { registerPrepareConfigTool } from "./tools/prepare-config";
import { KnowledgeCatalog, registerKnowledgeTemplate } from "./tools/knowledge";
import { registerHttpSessionRoutes } from "./utils/http-sessions";

/**
 * Read the package version from package.json at module load time.
 *
 * @implements REQ-REVIEW-011, SCN-REVIEW-011-01
 */
function getPackageVersion(): string {
  try {
    const packageJsonPath = path.join(__dirname, "..", "package.json");
    const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, "utf-8"));
    return packageJson.version || "0.0.0";
  } catch {
    return "0.0.0";
  }
}

// @implements REQ-REVIEW-011
const PACKAGE_VERSION = getPackageVersion();

/**
 * Fatal error codes that should cause the HTTP server to exit.
 *
 * @implements REQ-REVIEW-006, SCN-REVIEW-006-02
 */
const FATAL_ERROR_CODES = new Set(["EADDRINUSE", "EACCES", "ENOSPC", "EMFILE", "ENFILE"]);

/**
 * Main TLA+ MCP Server class
 */
export class TLAPlusMCPServer {
  private logger: Logger;
  private mcpLogLevel: LoggingLevel = "info";
  private catalog?: Promise<KnowledgeCatalog>;
  private httpServer?: http.Server;
  private closeSessions?: () => Promise<void>;
  private stdioServer?: McpServer;
  // @implements REQ-REVIEW-005, SCN-REVIEW-005-01
  private cachedKnowledgeBase: KnowledgeBaseEntry[] | null = null;

  constructor(private config: ServerConfig) {
    // Use stderr for stdio mode (stdout is reserved for MCP protocol)
    this.logger = new Logger(config.verbose, !config.http);
  }

  /**
   * Start the server in either stdio or HTTP mode
   */
  async start(): Promise<void> {
    if (this.config.http) {
      await this.startHttp();
    } else {
      await this.startStdio();
    }
  }

  /**
   * Start server in stdio mode (for Claude Desktop)
   */
  private async startStdio(): Promise<void> {
    this.logger.info("Starting TLA+ MCP server in stdio mode...");

    const server = await this.createMCPServer();
    this.stdioServer = server;
    const transport = new StdioServerTransport();

    await server.connect(transport);

    this.logger.info("TLA+ MCP server started successfully in stdio mode");
    this.logger.debug(`Configuration: ${JSON.stringify(this.config, null, 2)}`);
  }

  /**
   * Start server in HTTP mode (stateless)
   *
   * @implements REQ-REVIEW-005, SCN-REVIEW-005-01, SCN-REVIEW-005-02, SCN-REVIEW-005-03
   * @implements REQ-REVIEW-006, SCN-REVIEW-006-01, SCN-REVIEW-006-02
   */
  private async startHttp(): Promise<void> {
    // Pre-load knowledge base content (read files once at startup)
    // @implements REQ-REVIEW-005, SCN-REVIEW-005-01
    if (this.config.kbDir && !this.config.httpSession) {
      try {
        this.cachedKnowledgeBase = await this.loadKnowledgeBase(this.config.kbDir);
        this.logger.debug(`Knowledge base pre-loaded: ${this.cachedKnowledgeBase.length} articles`);
      } catch (error) {
        // @implements SCN-REVIEW-005-03
        this.logger.warn("Failed to pre-load knowledge base:", error);
        // Disable knowledge base usage for this HTTP server lifecycle
        this.config.kbDir = null;
      }
    }

    const app = express();
    applyHttpSecurity(app);
    app.use(express.json());

    if (this.config.httpSession) {
      this.closeSessions = registerHttpSessionRoutes(
        app,
        () => this.createMCPServer(true),
        (error) =>
          this.logger.error(
            "HTTP session error:",
            error instanceof Error ? error : new Error(String(error)),
          ),
      );
    } else {
      // POST /mcp - Handle MCP requests (stateless mode)
      app.post("/mcp", async (req, res) => {
        let serverInstance: McpServer | undefined;
        try {
          serverInstance = await this.createMCPServer();

          // Handle duplicate protocol version headers (fixes LiteLLM issues)
          const protocolVersion = req.headers["mcp-protocol-version"];
          if (
            protocolVersion &&
            typeof protocolVersion === "string" &&
            protocolVersion.includes(",")
          ) {
            req.headers["mcp-protocol-version"] = protocolVersion.split(",")[0].trim();
          }

          const transport = new StreamableHTTPServerTransport({
            sessionIdGenerator: undefined, // Stateless mode
          });

          res.on("close", () => {
            this.logger.debug("HTTP request closed");
            transport.close();
            if (serverInstance !== undefined) {
              serverInstance.close().catch((error) => {
                this.logger.error("Error closing MCP server instance:", error);
              });
              serverInstance = undefined;
            }
          });

          await serverInstance.connect(transport);
          await transport.handleRequest(req, res, req.body);
        } catch (error) {
          if (serverInstance !== undefined) {
            serverInstance.close().catch((closeError) => {
              this.logger.error("Error closing MCP server instance after failure:", closeError);
            });
            serverInstance = undefined;
          }
          this.logger.error("Error handling MCP request:", error as Error);
          if (!res.headersSent) {
            res.status(500).json({
              jsonrpc: "2.0",
              error: {
                code: -32603,
                message: "Internal server error",
              },
              id: null,
            });
          }
        }
      });

      // GET /mcp - Return 405 (stateless mode doesn't support SSE)
      app.get("/mcp", (req, res) => {
        res.status(405).json({
          jsonrpc: "2.0",
          error: {
            code: -32000,
            message: "Method not allowed. This server operates in stateless mode.",
          },
          id: null,
        });
      });

      // DELETE /mcp - Return 405 (stateless mode doesn't support session termination)
      app.delete("/mcp", (req, res) => {
        res.status(405).json({
          jsonrpc: "2.0",
          error: {
            code: -32000,
            message: "Method not allowed. This server operates in stateless mode.",
          },
          id: null,
        });
      });
    }

    // @implements REQ-REVIEW-006, SCN-REVIEW-006-01, SCN-REVIEW-006-02
    // Two-phase error handling: startup errors reject the promise,
    // operational errors discriminate between fatal and non-fatal.
    // Handlers are declared before app.listen() to avoid temporal dead zone.
    const _server = await new Promise<http.Server>((resolve, reject) => {
      // Startup phase: reject the promise so caller can handle the failure
      const startupErrorHandler = (err: NodeJS.ErrnoException) => {
        this.logger.error("Failed to start HTTP server:", err);
        reject(err);
      };

      // Operational phase: discriminate fatal vs non-fatal errors
      const operationalErrorHandler = (err: NodeJS.ErrnoException) => {
        const code = err.code || "";
        if (FATAL_ERROR_CODES.has(code)) {
          this.logger.error(`Fatal HTTP server error [${code}]:`, err);
          process.exit(1);
        } else {
          this.logger.warn(`Non-fatal HTTP server error [${code}]:`, err);
        }
      };

      const httpServer = app.listen(this.config.port, "127.0.0.1", () => {
        const actualPort = (httpServer.address() as { port: number })?.port || this.config.port;
        this.logger.info(`TLA+ MCP server listening at http://localhost:${actualPort}/mcp`);
        this.logger.debug(`Configuration: ${JSON.stringify(this.config, null, 2)}`);

        // Remove startup handler; attach operational handler
        httpServer.removeListener("error", startupErrorHandler);
        httpServer.on("error", operationalErrorHandler);
        resolve(httpServer);
      });

      httpServer.on("error", startupErrorHandler);
    });
    this.httpServer = _server;
    // No duplicate server.on('error') -- removed per SCN-REVIEW-006-01
  }

  /**
   * Create an MCP server instance with tools and resources
   *
   * @implements REQ-REVIEW-011, SCN-REVIEW-011-01
   * @implements REQ-REVIEW-005, SCN-REVIEW-005-02
   */
  async createMCPServer(
    persistent = !this.config.http || Boolean(this.config.httpSession),
  ): Promise<McpServer> {
    const server = new McpServer(
      {
        name: "TLA+ MCP Tools",
        // @implements REQ-REVIEW-011, SCN-REVIEW-011-01
        version: PACKAGE_VERSION,
      },
      {
        capabilities: {
          resources: {}, // Enable resource support
          logging: {},
        },
      },
    );

    let logLevel: LoggingLevel = "info";
    server.server.setRequestHandler(SetLevelRequestSchema, async (request) => {
      if (persistent) logLevel = request.params.level;
      else this.mcpLogLevel = request.params.level;
      return {};
    });

    // Register SANY tools (parse, symbol, modules)
    await registerSanyTools(server, this.config);
    this.logger.debug("SANY tools registered");

    // Register TLC tools (check, smoke, explore, trace)
    await registerTlcTools(server, this.config, (level, message, context) =>
      this.sendLog(level, message, context, persistent ? logLevel : this.mcpLogLevel),
    );
    this.logger.debug("TLC tools registered");

    // Register animation tools (detect, render, frameCount)
    await registerAnimationTools(server, this.config);
    this.logger.debug("Animation tools registered");

    await registerWorkflowPrompts(server, this.config);
    registerPrepareConfigTool(server);

    // Register knowledge base resources:
    // Use cached content if available (HTTP mode), otherwise read from disk (stdio mode)
    // @implements REQ-REVIEW-005, SCN-REVIEW-005-01, SCN-REVIEW-005-02
    if (persistent && this.config.kbDir) {
      this.catalog ??= KnowledgeCatalog.fromDirectory(this.config.kbDir);
      try {
        const catalog = await this.catalog;
        await catalog.refresh();
        catalog.register(server);
      } catch (error) {
        this.catalog = undefined;
        this.logger.warn("Knowledge base unavailable:", error);
      }
    } else if (this.cachedKnowledgeBase) {
      await registerKnowledgeBaseFromCache(server, this.cachedKnowledgeBase);
      registerKnowledgeTemplate(server, this.cachedKnowledgeBase);
      this.logger.debug("Knowledge base resources registered (from cache)");
    } else if (this.config.kbDir) {
      await registerKnowledgeBaseResources(server, this.config.kbDir);
      this.logger.debug("Knowledge base resources registered");
    } else {
      this.logger.info("Knowledge base directory not configured, skipping resource registration");
    }

    const sdkClose = server.close.bind(server);
    const onClose = server.server.onclose;
    let disposed = false;
    server.server.onclose = () => {
      if (disposed) return;
      disposed = true;
      onClose?.();
    };
    server.close = async () => {
      // SDK close has no onclose event until a transport exists.
      if (!server.server.transport) server.server.onclose?.();
      await sdkClose();
    };
    return server;
  }

  async sendLog(
    level: LoggingLevel,
    message: string,
    context?: ToolContext,
    minimum = this.mcpLogLevel,
  ): Promise<void> {
    if (!context?.sendNotification || context.signal?.aborted) return;
    if (LoggingLevelSchema.options.indexOf(level) < LoggingLevelSchema.options.indexOf(minimum))
      return;
    await context.sendNotification({
      method: "notifications/message",
      params: { level, logger: "tlc", data: { message } },
    });
  }

  async close(): Promise<void> {
    await this.closeSessions?.();
    await this.stdioServer?.close();
    if (this.httpServer) {
      const listener = this.httpServer;
      this.httpServer = undefined;
      listener.closeAllConnections();
      await new Promise<void>((resolve) => listener.close(() => resolve()));
    }
  }

  /**
   * Load knowledge base content from disk for caching.
   *
   * @implements REQ-REVIEW-005, SCN-REVIEW-005-01
   */
  private async loadKnowledgeBase(kbDir: string): Promise<KnowledgeBaseEntry[]> {
    const files = await fs.promises.readdir(kbDir);
    const markdownFiles = files.filter((f) => f.endsWith(".md"));
    const entries: KnowledgeBaseEntry[] = [];
    for (const fileName of markdownFiles) {
      const filePath = path.join(kbDir, fileName);
      const content = await fs.promises.readFile(filePath, "utf-8");
      const metadata = parseMarkdownFrontmatter(content);
      entries.push({
        fileName,
        resourceUri: `tlaplus://knowledge/${fileName}`,
        title: metadata.title || fileName,
        description: metadata.description || `TLA+ knowledge base article: ${fileName}`,
        content,
      });
    }
    return entries;
  }
}
