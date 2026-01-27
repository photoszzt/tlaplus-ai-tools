/**
 * Custom assertion helpers for MCP responses
 */

export function expectMcpTextResponse(response: any, expectedText: string): void {
  expect(response).toBeDefined();
  expect(response.content).toBeDefined();
  expect(Array.isArray(response.content)).toBe(true);
  expect(response.content).toHaveLength(1);
  expect(response.content[0].type).toBe('text');
  expect(response.content[0].text).toContain(expectedText);
}

export function expectMcpErrorResponse(response: any, errorText: string): void {
  expect(response).toBeDefined();
  expect(response.content).toBeDefined();
  expect(Array.isArray(response.content)).toBe(true);
  expect(response.content.length).toBeGreaterThan(0);
  expect(response.content[0].type).toBe('text');
  expect(response.content[0].text).toContain(errorText);
}

export function expectToolRegistered(
  server: any,
  toolName: string
): void {
  const tools = server.getRegisteredTools();
  expect(tools.has(toolName)).toBe(true);

  const tool = tools.get(toolName);
  expect(tool).toBeDefined();
  expect(tool.name).toBe(toolName);
  expect(tool.description).toBeTruthy();
  expect(tool.schema).toBeDefined();
  expect(typeof tool.handler).toBe('function');
}

export function expectResourceRegistered(
  server: any,
  resourceUri: string
): void {
  const resources = server.getRegisteredResources();
  expect(resources.has(resourceUri)).toBe(true);

  const resource = resources.get(resourceUri);
  expect(resource).toBeDefined();
  expect(resource.uri).toBe(resourceUri);
  expect(resource.name).toBeTruthy();
  expect(typeof resource.handler).toBe('function');
}

export function expectMcpJsonResponse(response: any): any {
  expect(response).toBeDefined();
  expect(response.content).toBeDefined();
  expect(response.content).toHaveLength(1);
  expect(response.content[0].type).toBe('text');

  // Parse JSON from text content
  const parsed = JSON.parse(response.content[0].text);
  return parsed;
}
