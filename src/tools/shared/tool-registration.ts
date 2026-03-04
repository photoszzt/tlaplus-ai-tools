// Shared tool registration helper that wraps McpServer.tool() to avoid
// TS2589 "Type instantiation is excessively deep" errors caused by the
// MCP SDK's heavily overloaded tool() method combined with Zod schemas.
//
// The server parameter is typed as McpServer (REQ-REVIEW-002). This helper
// provides a simplified call signature that avoids deep generic inference
// while preserving full runtime behavior.
//
// Spec: docs/review-remediation/spec.md
// Contract: docs/review-remediation/contract.md

import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import type { CallToolResult } from '@modelcontextprotocol/sdk/types.js';

/**
 * Register a tool on the McpServer with a simplified type signature.
 *
 * This avoids TS2589 by not requiring TypeScript to resolve the deeply-nested
 * generic overloads on McpServer.tool(). The callback parameters are explicitly
 * typed at each call site for runtime safety.
 *
 * The paramsSchema parameter accepts any Zod shape object. We use
 * Record<string, unknown> here instead of ZodRawShapeCompat to avoid
 * triggering the same deep type instantiation in the MCP SDK's type
 * resolution between Zod v3 and v4.
 *
 * @implements REQ-REVIEW-002 (typed server parameter workaround for MCP SDK limitation)
 */
export function registerTool(
  server: McpServer,
  name: string,
  description: string,
  paramsSchema: Record<string, unknown>,
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  callback: (args: any, extra: any) => CallToolResult | Promise<CallToolResult>
): void {
  // Use Function cast to bypass the overloaded tool() type resolution.
  // At runtime, this calls server.tool(name, description, paramsSchema, callback)
  // exactly as before -- only the compile-time type checking is simplified.
  (server.tool as Function).call(server, name, description, paramsSchema, callback);
}
