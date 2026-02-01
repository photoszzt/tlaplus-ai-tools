# MCP Timeout Configuration

## Overview

TLA+ MCP tools can run for extended periods, especially during model checking operations. This document explains how timeouts work and how to configure them to prevent premature request cancellation.

## Server-Side Timeouts

The TLA+ MCP server implements tool-level timeouts to prevent runaway processes:

### Default Timeouts

- **`tlaplus_mcp_tlc_check`**: No default timeout (exhaustive model checking can take arbitrarily long)
- **`tlaplus_mcp_tlc_smoke`**: 2 minutes (120,000ms)
- **`tlaplus_mcp_tlc_explore`**: 10 minutes (600,000ms)

### Environment Variables

You can override default timeouts using environment variables:

```bash
export TLC_SMOKE_TIMEOUT_MS=300000    # 5 minutes
export TLC_EXPLORE_TIMEOUT_MS=1200000 # 20 minutes
```

### Per-Request Timeouts

Tools that support timeouts accept an optional `timeoutMs` parameter:

```json
{
  "method": "tools/call",
  "params": {
    "name": "tlaplus_mcp_tlc_smoke",
    "arguments": {
      "fileName": "/path/to/spec.tla",
      "timeoutMs": 180000
    }
  }
}
```

## Host-Side Timeouts

MCP clients (hosts) may impose their own request timeouts. The TLA+ MCP server sends **progress notifications** to prevent hosts from timing out long-running operations.

### Progress Notifications

When a client includes a `progressToken` in the request metadata, the server will send periodic `notifications/progress` messages:

```json
{
  "jsonrpc": "2.0",
  "method": "notifications/progress",
  "params": {
    "progressToken": "unique-token-123",
    "progress": 150,
    "total": 500,
    "message": "Processing TLC output: 150/500 lines"
  }
}
```

Progress updates are sent approximately every **10 seconds** during output processing.

### Client Configuration

#### Claude Desktop

Claude Desktop uses the MCP TypeScript SDK, which supports:

- **`resetTimeoutOnProgress`**: Resets the request timeout each time a progress notification is received
- **`maxTotalTimeout`**: Maximum total time to wait, regardless of progress notifications

Example client-side request options:

```typescript
await client.request(
  {
    method: "tools/call",
    params: {
      name: "tlaplus_mcp_tlc_smoke",
      arguments: { fileName: "/path/to/spec.tla" },
      _meta: { progressToken: "token-123" }
    }
  },
  CallToolResultSchema,
  {
    timeout: 60000,              // Initial timeout: 1 minute
    resetTimeoutOnProgress: true, // Reset on each progress notification
    maxTotalTimeout: 600000       // Hard limit: 10 minutes
  }
);
```

#### Other MCP Clients

If your MCP client does not support `resetTimeoutOnProgress`, you have two options:

1. **Increase the client-side timeout** to accommodate the longest expected operation
2. **Use task-augmented execution** (if supported by your client) to poll for results asynchronously

## Timeout Behavior

### When a Timeout Occurs

If a tool operation times out:

1. The TLC process is terminated (SIGTERM, then SIGKILL if needed)
2. Partial output collected so far is returned
3. The response includes a timeout marker: `"TLC process timed out after Xms."`
4. Exit code is set to `124` (standard timeout exit code)

### When a Request is Aborted

If the client cancels the request (via `AbortSignal`):

1. The TLC process is terminated immediately
2. Partial output is returned
3. The response includes: `"TLC process was aborted."`
4. Exit code is set to `130` (standard interrupt exit code)

## Recommendations

### For Short Operations (< 2 minutes)

Use `tlaplus_mcp_tlc_smoke` with default settings. No special configuration needed.

### For Medium Operations (2-10 minutes)

Use `tlaplus_mcp_tlc_explore` with:
- Server-side timeout: 10 minutes (default)
- Client-side: Enable `resetTimeoutOnProgress` if available

### For Long Operations (> 10 minutes)

Use `tlaplus_mcp_tlc_check` with:
- Server-side timeout: Set via `timeoutMs` parameter or disable entirely
- Client-side: Use `maxTotalTimeout` to set a hard limit
- Consider using task-augmented execution for operations > 30 minutes

### For Exhaustive Model Checking

`tlaplus_mcp_tlc_check` has no default timeout because exhaustive model checking can take hours or days. You should:

1. Set an explicit `timeoutMs` based on your model's expected runtime
2. Use `maxTotalTimeout` on the client side as a safety net
3. Monitor progress notifications to track execution
4. Consider running large model checks outside of MCP (e.g., via CLI) and using MCP only for smaller verification tasks

## Troubleshooting

### "RequestTimeout" Error (Code -32001)

This means the MCP client gave up waiting for a response. Solutions:

1. **Enable progress notifications**: Ensure your client includes `progressToken` in `_meta`
2. **Enable `resetTimeoutOnProgress`**: If your client supports it
3. **Increase client timeout**: Set a higher `timeout` value
4. **Increase server timeout**: Use `timeoutMs` parameter or environment variables

### Partial Output Returned

If you receive partial output with a timeout message:

1. The operation exceeded the configured timeout
2. Increase the timeout using `timeoutMs` parameter
3. Check if the model is too large for interactive verification
4. Consider optimizing your TLA+ specification or using smaller test cases

### No Progress Notifications

If you're not receiving progress notifications:

1. Verify your client includes `progressToken` in the request `_meta`
2. Check that your client supports receiving `notifications/progress`
3. Progress is only sent during output processing (after TLC completes)
4. If TLC hangs before producing output, no progress will be sent

## Implementation Details

### Progress Notification Frequency

Progress notifications are sent at most once every **10 seconds** during output processing. This prevents flooding the client with notifications while still providing regular heartbeats.

### Process Management

The server uses robust process management:

- **Process groups** (Linux) to ensure child processes are terminated
- **SIGTERM → SIGKILL escalation** with 5-second grace period
- **Stream draining** to prevent hangs on process termination
- **Bounded output buffers** (1MB default) to prevent memory exhaustion

### Compatibility

Progress notifications are fully compatible with the MCP specification (DRAFT-2026-v1) and work with any compliant MCP client.
