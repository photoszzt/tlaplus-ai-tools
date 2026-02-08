import { TLAPlusMCPServer } from '../server';
import { ServerConfig } from '../types';
import { MINIMAL_CONFIG, HTTP_CONFIG, FULL_CONFIG } from './fixtures/config-samples';

// Mock MCP SDK
jest.mock('@modelcontextprotocol/sdk/server/mcp.js');
jest.mock('@modelcontextprotocol/sdk/server/stdio.js');
jest.mock('@modelcontextprotocol/sdk/server/streamableHttp.js');

// Mock tool registration functions
jest.mock('../tools/sany');
jest.mock('../tools/tlc');
jest.mock('../tools/knowledge');
jest.mock('../tools/animation');

// Mock express
jest.mock('express');

import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import { registerSanyTools } from '../tools/sany';
import { registerTlcTools } from '../tools/tlc';
import { registerKnowledgeBaseResources } from '../tools/knowledge';
import { registerAnimationTools } from '../tools/animation';
import express, { Express, Request, Response } from 'express';

describe('TLAPlusMCPServer', () => {
  let mockMcpServer: any;
  let mockStdioTransport: any;
  let mockHttpTransport: any;
  let mockExpressApp: any;
  let mockHttpServer: any;

  beforeEach(() => {
    jest.clearAllMocks();

    // Mock McpServer
    mockMcpServer = {
      connect: jest.fn().mockResolvedValue(undefined),
      close: jest.fn().mockResolvedValue(undefined)
    };
    (McpServer as jest.Mock).mockImplementation(() => mockMcpServer);

    // Mock StdioServerTransport
    mockStdioTransport = {};
    (StdioServerTransport as jest.Mock).mockImplementation(() => mockStdioTransport);

    // Mock StreamableHTTPServerTransport
    mockHttpTransport = {
      handleRequest: jest.fn().mockResolvedValue(undefined),
      close: jest.fn()
    };
    (StreamableHTTPServerTransport as jest.Mock).mockImplementation(() => mockHttpTransport);

    // Mock Express
    mockHttpServer = {
      listen: jest.fn((port, callback) => {
        setImmediate(() => callback());
        return mockHttpServer;
      }),
      on: jest.fn(),
      address: jest.fn(() => ({ port: 3000 }))
    };

    mockExpressApp = {
      use: jest.fn(),
      post: jest.fn(),
      get: jest.fn(),
      delete: jest.fn(),
      listen: jest.fn((port, callback) => {
        setImmediate(() => callback());
        return mockHttpServer;
      })
    };
    (express as unknown as jest.Mock).mockReturnValue(mockExpressApp);
    (express.json as jest.Mock) = jest.fn();

    // Mock tool registration
    (registerSanyTools as jest.Mock).mockResolvedValue(undefined);
    (registerTlcTools as jest.Mock).mockResolvedValue(undefined);
    (registerKnowledgeBaseResources as jest.Mock).mockResolvedValue(undefined);
    (registerAnimationTools as jest.Mock).mockResolvedValue(undefined);
  });

  describe('Constructor', () => {
    it('creates server with minimal config', () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      expect(server).toBeInstanceOf(TLAPlusMCPServer);
    });

    it('creates server with full config', () => {
      const server = new TLAPlusMCPServer(FULL_CONFIG);
      expect(server).toBeInstanceOf(TLAPlusMCPServer);
    });

    it('creates server with HTTP config', () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      expect(server).toBeInstanceOf(TLAPlusMCPServer);
    });
  });

  describe('Server Initialization', () => {
    it('creates MCP server with correct metadata', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(McpServer).toHaveBeenCalledWith(
        {
          name: 'TLA+ MCP Tools',
          version: '1.0.0'
        },
        {
          capabilities: {
            resources: {}
          }
        }
      );
    });

    it('registers SANY tools', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(registerSanyTools).toHaveBeenCalledWith(mockMcpServer, MINIMAL_CONFIG);
    });

    it('registers TLC tools', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(registerTlcTools).toHaveBeenCalledWith(mockMcpServer, MINIMAL_CONFIG);
    });

    it('registers animation tools', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(registerAnimationTools).toHaveBeenCalledWith(mockMcpServer, MINIMAL_CONFIG);
    });

    it('registers knowledge base resources when kbDir provided', async () => {
      const server = new TLAPlusMCPServer(FULL_CONFIG);
      await server.start();

      expect(registerKnowledgeBaseResources).toHaveBeenCalledWith(
        mockMcpServer,
        FULL_CONFIG.kbDir
      );
    });

    it('skips knowledge base registration when kbDir not provided', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(registerKnowledgeBaseResources).not.toHaveBeenCalled();
    });
  });

  describe('Stdio Mode', () => {
    it('starts server in stdio mode by default', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(StdioServerTransport).toHaveBeenCalledTimes(1);
      expect(mockMcpServer.connect).toHaveBeenCalledWith(mockStdioTransport);
    });

    it('does not start HTTP server in stdio mode', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(express).not.toHaveBeenCalled();
    });

    it('connects transport to MCP server', async () => {
      const server = new TLAPlusMCPServer(MINIMAL_CONFIG);
      await server.start();

      expect(mockMcpServer.connect).toHaveBeenCalledTimes(1);
      expect(mockMcpServer.connect).toHaveBeenCalledWith(mockStdioTransport);
    });
  });

  describe('HTTP Mode', () => {
    it('starts server in HTTP mode when configured', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(express).toHaveBeenCalledTimes(1);
      expect(mockExpressApp.use).toHaveBeenCalledWith(express.json());
      expect(mockExpressApp.listen).toHaveBeenCalledWith(
        HTTP_CONFIG.port,
        expect.any(Function)
      );
    });

    it('does not create stdio transport in HTTP mode', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(StdioServerTransport).not.toHaveBeenCalled();
    });

    it('registers POST /mcp endpoint', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(mockExpressApp.post).toHaveBeenCalledWith('/mcp', expect.any(Function));
    });

    it('registers GET /mcp endpoint', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(mockExpressApp.get).toHaveBeenCalledWith('/mcp', expect.any(Function));
    });

    it('registers DELETE /mcp endpoint', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(mockExpressApp.delete).toHaveBeenCalledWith('/mcp', expect.any(Function));
    });

    it('registers error handler for server', async () => {
      const server = new TLAPlusMCPServer(HTTP_CONFIG);
      await server.start();

      expect(mockHttpServer.on).toHaveBeenCalledWith('error', expect.any(Function));
    });

    describe('POST /mcp endpoint', () => {
      let postHandler: (req: any, res: any) => Promise<void>;

      beforeEach(async () => {
        const server = new TLAPlusMCPServer(HTTP_CONFIG);
        await server.start();

        // Extract the POST handler
        const postCall = (mockExpressApp.post as jest.Mock).mock.calls.find(
          call => call[0] === '/mcp'
        );
        postHandler = postCall[1];
      });

      it('creates new MCP server instance per request', async () => {
        const mockReq = {
          headers: {},
          body: {},
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn(),
          headersSent: false,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(McpServer).toHaveBeenCalled();
        expect(StreamableHTTPServerTransport).toHaveBeenCalled();
      });

      it('handles duplicate protocol version headers', async () => {
        const mockReq = {
          headers: {
            'mcp-protocol-version': '1.0, 1.0'
          },
          body: {},
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn(),
          headersSent: false,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(mockReq.headers['mcp-protocol-version']).toBe('1.0');
      });

      it('connects transport to server and handles request', async () => {
        const mockReq = {
          headers: {},
          body: { test: 'data' },
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn(),
          headersSent: false,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(mockMcpServer.connect).toHaveBeenCalledWith(mockHttpTransport);
        expect(mockHttpTransport.handleRequest).toHaveBeenCalledWith(
          mockReq,
          mockRes,
          { test: 'data' }
        );
      });

      it('cleans up transport and server on response close', async () => {
        let closeCallback: (() => void) | undefined;
        const mockReq = {
          headers: {},
          body: {},
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn((event, callback) => {
            if (event === 'close') {
              closeCallback = callback;
            }
          }),
          headersSent: false,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(closeCallback).toBeDefined();
        closeCallback!();

        expect(mockHttpTransport.close).toHaveBeenCalled();
        expect(mockMcpServer.close).toHaveBeenCalled();
      });

      it('returns 500 on error', async () => {
        mockMcpServer.connect.mockRejectedValue(new Error('Connection failed'));

        const mockReq = {
          headers: {},
          body: {},
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn(),
          headersSent: false,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(mockRes.status).toHaveBeenCalledWith(500);
        expect(mockRes.json).toHaveBeenCalledWith({
          jsonrpc: '2.0',
          error: {
            code: -32603,
            message: 'Internal server error'
          },
          id: null
        });
      });

      it('does not send response if headers already sent', async () => {
        mockMcpServer.connect.mockRejectedValue(new Error('Connection failed'));

        const mockReq = {
          headers: {},
          body: {},
          on: jest.fn()
        };
        const mockRes = {
          on: jest.fn(),
          headersSent: true,
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        await postHandler(mockReq, mockRes);

        expect(mockRes.status).not.toHaveBeenCalled();
        expect(mockRes.json).not.toHaveBeenCalled();
      });
    });

    describe('GET /mcp endpoint', () => {
      it('returns 405 Method Not Allowed', async () => {
        const server = new TLAPlusMCPServer(HTTP_CONFIG);
        await server.start();

        const getCall = (mockExpressApp.get as jest.Mock).mock.calls.find(
          call => call[0] === '/mcp'
        );
        const getHandler = getCall[1];

        const mockRes = {
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        getHandler({}, mockRes);

        expect(mockRes.status).toHaveBeenCalledWith(405);
        expect(mockRes.json).toHaveBeenCalledWith({
          jsonrpc: '2.0',
          error: {
            code: -32000,
            message: 'Method not allowed. This server operates in stateless mode.'
          },
          id: null
        });
      });
    });

    describe('DELETE /mcp endpoint', () => {
      it('returns 405 Method Not Allowed', async () => {
        const server = new TLAPlusMCPServer(HTTP_CONFIG);
        await server.start();

        const deleteCall = (mockExpressApp.delete as jest.Mock).mock.calls.find(
          call => call[0] === '/mcp'
        );
        const deleteHandler = deleteCall[1];

        const mockRes = {
          status: jest.fn().mockReturnThis(),
          json: jest.fn()
        };

        deleteHandler({}, mockRes);

        expect(mockRes.status).toHaveBeenCalledWith(405);
        expect(mockRes.json).toHaveBeenCalledWith({
          jsonrpc: '2.0',
          error: {
            code: -32000,
            message: 'Method not allowed. This server operates in stateless mode.'
          },
          id: null
        });
      });
    });
  });
});
