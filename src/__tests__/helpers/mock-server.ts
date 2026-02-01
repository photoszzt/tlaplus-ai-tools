/**
 * Mock MCP server for testing tool registration
 */

export interface MockTool {
  name: string;
  description: string;
  schema: any;
  handler: (args: any, context?: any) => Promise<any>;
}

export interface MockResource {
  uri: string;
  name: string;
  metadata: any;
  handler: () => Promise<any>;
}

export function createMockMcpServer() {
  const tools = new Map<string, MockTool>();
  const resources = new Map<string, MockResource>();

  return {
    tool: jest.fn((name: string, description: string, schema: any, handler: (args: any, context?: any) => Promise<any>) => {
      tools.set(name, { name, description, schema, handler });
    }),
    resource: jest.fn((uri: string, name: string, metadata: any, handler: () => Promise<any>) => {
      resources.set(uri, { uri, name, metadata, handler });
    }),
    getRegisteredTools: () => tools,
    getRegisteredResources: () => resources,
    connect: jest.fn().mockResolvedValue(undefined),
    close: jest.fn().mockResolvedValue(undefined)
  };
}

export async function callRegisteredTool(
  server: ReturnType<typeof createMockMcpServer>,
  toolName: string,
  args: any,
  context?: any
): Promise<any> {
  const tool = server.getRegisteredTools().get(toolName);
  if (!tool) {
    throw new Error(`Tool ${toolName} not registered`);
  }
  return await tool.handler(args, context);
}

export async function callRegisteredResource(
  server: ReturnType<typeof createMockMcpServer>,
  resourceUri: string
): Promise<any> {
  const resource = server.getRegisteredResources().get(resourceUri);
  if (!resource) {
    throw new Error(`Resource ${resourceUri} not registered`);
  }
  return await resource.handler();
}
