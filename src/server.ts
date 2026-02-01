import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import express from 'express';
import * as http from 'http';
import { z } from 'zod';
import { ServerConfig } from './types';
import { Logger } from './utils/logging';
import { registerSanyTools } from './tools/sany';
import { registerTlcTools } from './tools/tlc';
import { registerKnowledgeBaseResources } from './tools/knowledge';

/**
 * Main TLA+ MCP Server class
 */
export class TLAPlusMCPServer {
  private logger: Logger;

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
    this.logger.info('Starting TLA+ MCP server in stdio mode...');

    const server = await this.createMCPServer();
    const transport = new StdioServerTransport();

    await server.connect(transport);

    this.logger.info('TLA+ MCP server started successfully in stdio mode');
    this.logger.debug(`Configuration: ${JSON.stringify(this.config, null, 2)}`);
  }

  /**
   * Start server in HTTP mode (stateless)
   */
  private async startHttp(): Promise<void> {
    const app = express();
    app.use(express.json());

    // POST /mcp - Handle MCP requests (stateless mode)
    app.post('/mcp', async (req, res) => {
      let serverInstance: McpServer | undefined;
      try {
        serverInstance = await this.createMCPServer();

        // Handle duplicate protocol version headers (fixes LiteLLM issues)
        const protocolVersion = req.headers['mcp-protocol-version'];
        if (protocolVersion && typeof protocolVersion === 'string' && protocolVersion.includes(',')) {
          req.headers['mcp-protocol-version'] = protocolVersion.split(',')[0].trim();
        }

        const transport = new StreamableHTTPServerTransport({
          sessionIdGenerator: undefined // Stateless mode
        });

        res.on('close', () => {
          this.logger.debug('HTTP request closed');
          transport.close();
          if (serverInstance !== undefined) {
            serverInstance.close().catch(error => {
              this.logger.error('Error closing MCP server instance:', error);
            });
            serverInstance = undefined;
          }
        });

        await serverInstance.connect(transport);
        await transport.handleRequest(req, res, req.body);
      } catch (error) {
        if (serverInstance !== undefined) {
          serverInstance.close().catch(closeError => {
            this.logger.error('Error closing MCP server instance after failure:', closeError);
          });
          serverInstance = undefined;
        }
        this.logger.error('Error handling MCP request:', error as Error);
        if (!res.headersSent) {
          res.status(500).json({
            jsonrpc: '2.0',
            error: {
              code: -32603,
              message: 'Internal server error',
            },
            id: null,
          });
        }
      }
    });

    // GET /mcp - Return 405 (stateless mode doesn't support SSE)
    app.get('/mcp', (req, res) => {
      res.status(405).json({
        jsonrpc: '2.0',
        error: {
          code: -32000,
          message: 'Method not allowed. This server operates in stateless mode.'
        },
        id: null
      });
    });

    // DELETE /mcp - Return 405 (stateless mode doesn't support session termination)
    app.delete('/mcp', (req, res) => {
      res.status(405).json({
        jsonrpc: '2.0',
        error: {
          code: -32000,
          message: 'Method not allowed. This server operates in stateless mode.'
        },
        id: null
      });
    });

    // Start HTTP server
    const server = await new Promise<http.Server>((resolve) => {
      const httpServer = app.listen(this.config.port, () => {
        const actualPort = (httpServer.address() as { port: number })?.port || this.config.port;
        this.logger.info(`TLA+ MCP server listening at http://localhost:${actualPort}/mcp`);
        this.logger.debug(`Configuration: ${JSON.stringify(this.config, null, 2)}`);
        resolve(httpServer);
      });

      httpServer.on('error', (err) => {
        this.logger.error('Failed to start HTTP server:', err);
        process.exit(1);
      });
    });

    server.on('error', (err) => {
      this.logger.error('Failed to start HTTP server:', err);
      process.exit(1);
    });
  }

  /**
   * Create an MCP server instance with tools and resources
   */
  private async createMCPServer(): Promise<McpServer> {
    const server = new McpServer(
      {
        name: 'TLA+ MCP Tools',
        version: '1.0.0',
      },
      {
        capabilities: {
          resources: {}  // Enable resource support
        }
      }
    );

    // Register SANY tools (parse, symbol, modules)
    await registerSanyTools(server, this.config);
    this.logger.debug('SANY tools registered');

    // Register TLC tools (check, smoke, explore, trace)
    await registerTlcTools(server, this.config);
    this.logger.debug('TLC tools registered');

    // Register knowledge base resources if configured
    if (this.config.kbDir) {
      await registerKnowledgeBaseResources(server, this.config.kbDir);
      this.logger.debug('Knowledge base resources registered');
    } else {
      this.logger.info('Knowledge base directory not configured, skipping resource registration');
    }

    return server;
  }
}
