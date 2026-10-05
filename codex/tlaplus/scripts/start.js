#!/usr/bin/env node

const fs = require("node:fs");
const path = require("node:path");

const root = path.resolve(__dirname, "..");
const entry = path.join(root, "dist", "index.js");
process.chdir(root);

if (!fs.existsSync(entry)) {
  process.stderr.write("TLA+ MCP server build is missing: dist/index.js\n");
  process.exit(1);
}

try {
  require.resolve("@modelcontextprotocol/sdk/server/index.js");
} catch {
  process.stderr.write("TLA+ MCP runtime dependencies are missing. Install the dependencies declared in the plugin's package.json before starting the server.\n");
  process.exit(1);
}

require(entry);
