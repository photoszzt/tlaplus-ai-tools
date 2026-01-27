# TLA+ MCP Server

Model Context Protocol (MCP) server for TLA+ formal specification tools.

## Overview

This package provides a standalone MCP server that exposes TLA+ tools (SANY parser, TLC model checker) and knowledge base resources to MCP clients like Claude Desktop and other AI assistants.

## Features

- **Parse & Validate** - Parse TLA+ specifications using SANY to detect syntax and semantic errors
- **Model Checking** - Run exhaustive model checking with TLC to verify correctness properties
- **Smoke Testing** - Quick random simulation to find violations without exhaustive state exploration
- **Behavior Exploration** - Generate and inspect behavior traces of specified lengths
- **Symbol Extraction** - Extract symbols from TLA+ modules with TLC config suggestions
- **Module Discovery** - List available TLA+ standard modules
- **Knowledge Base** - Access 20+ articles on TLA+ best practices and common patterns

## Installation

### From Source

```bash
git clone https://github.com/USER/tlaplus-mcp-server.git
cd tlaplus-mcp-server

# Install dependencies
npm install

# Build
npm run build

# Run setup to download TLA+ tools
npm run setup

# Link globally (optional)
npm link
```

## Requirements

- **Node.js**: 18.0.0 or higher
- **Java**: 11 or higher (required for TLA+ tools)
- **TLA+ Tools**: tla2tools.jar and CommunityModules-deps.jar (downloaded by setup script)

## Usage

### Stdio Mode (for Claude Desktop)

The server runs in stdio mode by default, suitable for Claude Desktop integration:

```bash
tlaplus-mcp-server [options]
```

### HTTP Mode

For remote access or non-stdio clients:

```bash
tlaplus-mcp-server --http --port 3000
```

### CLI Options

- `--http` - Enable HTTP transport (default: stdio)
- `--port <number>` - HTTP server port (default: 3000)
- `--working-dir <path>` - Restrict file access to this directory
- `--tools-dir <path>` - Path to TLA+ tools directory (auto-detected if omitted)
- `--kb-dir <path>` - Path to knowledge base directory (auto-detected if omitted)
- `--java-home <path>` - Path to Java installation (uses system Java if omitted)
- `--verbose` - Enable debug logging
- `--help, -h` - Show help message
- `--version, -v` - Show version

### Examples

```bash
# Start in stdio mode with auto-detection
tlaplus-mcp-server

# Start in HTTP mode with verbose logging
tlaplus-mcp-server --http --port 3000 --verbose

# Specify custom paths
tlaplus-mcp-server --tools-dir /opt/tlaplus/tools --kb-dir /opt/tlaplus/kb

# Restrict to project directory
tlaplus-mcp-server --working-dir /home/user/my-tla-project

# Use specific Java installation
tlaplus-mcp-server --java-home /usr/lib/jvm/java-17-openjdk
```

## Claude Code Configuration

### Installation

1. Install the TLA+ MCP Server plugin:

```bash
cd tlaplus-mcp-server
npm run setup  # Download TLA+ tools
npm link       # Make globally available
```

2. Add to your Claude Code config file:

**macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
**Windows**: `%APPDATA%/Claude/claude_desktop_config.json`
**Linux**: `~/.config/Claude/claude_desktop_config.json`

### Minimal Configuration

```json
{
  "mcpServers": {
    "tlaplus": {
      "command": "tlaplus-mcp-server"
    }
  }
}
```

### With Custom Paths

```json
{
  "mcpServers": {
    "tlaplus": {
      "command": "tlaplus-mcp-server",
      "args": [
        "--tools-dir", "/path/to/tlaplus-mcp-server/tools",
        "--kb-dir", "/path/to/tlaplus-mcp-server/resources/knowledgebase",
        "--verbose"
      ]
    }
  }
}
```

### With Working Directory Restriction

```json
{
  "mcpServers": {
    "tlaplus": {
      "command": "tlaplus-mcp-server",
      "args": ["--working-dir", "/path/to/project"]
    }
  }
}
```

## OpenCode Configuration

### Installation

1. Install the TLA+ MCP Server plugin:

```bash
cd tlaplus-mcp-server
npm run setup  # Download TLA+ tools
npm link       # Make globally available
```

2. Add the plugin to your OpenCode configuration:

**Location**: `~/.config/opencode/plugin/tlaplus-mcp-server/`

Create `manifest.json`:

```json
{
  "name": "tlaplus-mcp-server",
  "version": "1.0.0",
  "description": "TLA+ formal specification tools for OpenCode",
  "type": "mcp",
  "mcp": {
    "command": "tlaplus-mcp-server",
    "args": []
  }
}
```

### With Custom Paths

```json
{
  "name": "tlaplus-mcp-server",
  "version": "1.0.0",
  "description": "TLA+ formal specification tools for OpenCode",
  "type": "mcp",
  "mcp": {
    "command": "tlaplus-mcp-server",
    "args": [
      "--tools-dir", "/path/to/tlaplus-mcp-server/tools",
      "--kb-dir", "/path/to/tlaplus-mcp-server/resources/knowledgebase",
      "--verbose"
    ]
  }
}
```

### Skills Integration

Create skill files in `~/.config/opencode/plugin/tlaplus-mcp-server/skills/`:

**tlaplus-parse.md**:
```markdown
# TLA+ Parse Skill

Use this skill when you need to parse and validate TLA+ specifications.

## When to Use
- Checking TLA+ syntax
- Validating module structure
- Detecting semantic errors

## Usage
Use the tlaplus_mcp_sany_parse tool with the file path.
```

**tlaplus-model-check.md**:
```markdown
# TLA+ Model Checking Skill

Use this skill when you need to verify TLA+ specifications.

## When to Use
- Exhaustive state space exploration
- Verifying invariants and properties
- Finding counterexamples

## Usage
Use the tlaplus_mcp_tlc_check tool with the file path and optional config.
```

## Available Tools

### SANY Tools

#### `tlaplus_mcp_sany_parse`
Parse a TLA+ module for syntax and semantic errors.

**Parameters:**
- `fileName` (string): Full path to the TLA+ file

**Example:**
```
Parse /path/to/MySpec.tla
```

#### `tlaplus_mcp_sany_symbol`
Extract symbols from a TLA+ module for TLC configuration file generation.

**Parameters:**
- `fileName` (string): Full path to the TLA+ file
- `includeExtendedModules` (boolean, optional): Include symbols from extended/instantiated modules

**Response format (schemaVersion: 1):**

```json
{
  "schemaVersion": 1,
  "rootModule": "Counter",
  "file": "/path/to/Counter.tla",
  "includeExtendedModules": false,
  "candidates": {
    "constants": [{ "name": "MaxValue", "location": {...}, "comment": "..." }],
    "variables": [{ "name": "count", "location": {...} }],
    "statePredicates": [{ "name": "Init", "location": {...} }],
    "actionPredicates": [{ "name": "Next", "location": {...} }],
    "temporalFormulas": [{ "name": "Spec", "location": {...} }],
    "operatorsWithArgs": [{ "name": "Add", "location": {...} }],
    "theorems": [...],
    "assumptions": [...]
  },
  "bestGuess": {
    "init": { "name": "Init", "match": "exact", "reason": "root module exact match" },
    "next": { "name": "Next", "match": "exact", "reason": "root module exact match" },
    "spec": { "name": "Spec", "match": "exact", "reason": "root module exact match" },
    "invariants": [{ "name": "TypeOK", "match": "contains", "reason": "..." }],
    "properties": [{ "name": "Liveness", "match": "contains", "reason": "..." }]
  },
  "extendedModules": {
    "Helper": { "candidates": {...} }
  }
}
```

**TLA+ Level meanings:**
- Level 0: Constant expressions
- Level 1: State expressions (can reference variables)
- Level 2: Action expressions (can reference primed variables)
- Level 3: Temporal formulas

**bestGuess matching:**
- `exact`: Exact name match (e.g., "Init")
- `case_insensitive_exact`: Case-insensitive exact match
- `prefix`: Name starts with expected prefix (e.g., "InitState")
- `contains`: Name contains expected pattern
- `fallback_first_candidate`: No name match, using first available candidate

**Module preference in bestGuess:**
1. Root module (highest priority)
2. Extended non-stdlib modules
3. Standard library modules (lowest priority, used as last resort)

#### `tlaplus_mcp_sany_modules`
List all available TLA+ standard modules.

**Parameters:** None

**Example:**
```
List available TLA+ modules
```

### TLC Tools

#### `tlaplus_mcp_tlc_check`
Perform exhaustive model checking on a TLA+ specification.

**Parameters:**
- `fileName` (string): Full path to the TLA+ file
- `cfgFile` (string, optional): Path to custom TLC configuration file
- `extraOpts` (array, optional): Additional TLC options
- `extraJavaOpts` (array, optional): Additional Java options

**Example:**
```
Model check /path/to/Counter.tla
```

**Note:** Requires a .cfg file (Counter.cfg or MCCounter.tla/MCCounter.cfg).

#### `tlaplus_mcp_tlc_smoke`
Run a quick smoke test using random simulation (3 seconds).

**Parameters:**
- `fileName` (string): Full path to the TLA+ file
- `cfgFile` (string, optional): Path to custom TLC configuration file
- `extraOpts` (array, optional): Additional TLC options
- `extraJavaOpts` (array, optional): Additional Java options

**Example:**
```
Smoke test /path/to/Counter.tla
```

#### `tlaplus_mcp_tlc_explore`
Generate and print a behavior trace of specified length.

**Parameters:**
- `fileName` (string): Full path to the TLA+ file
- `behaviorLength` (number): Length of behavior to generate
- `cfgFile` (string, optional): Path to custom TLC configuration file
- `extraOpts` (array, optional): Additional TLC options
- `extraJavaOpts` (array, optional): Additional Java options

**Example:**
```
Explore /path/to/Counter.tla with behavior length 5
```

## Knowledge Base Resources

The server exposes 20+ TLA+ knowledge base articles as MCP resources:

- `tla-animations.md` - Understanding TLA+ animations
- `tla-bestpractice-spec-properties.md` - Best practices for specifications
- `tla-choose-nondeterminism.md` - Using CHOOSE for nondeterminism
- `tla-functions-records-sequences.md` - Functions, records, and sequences
- `tla-refinement.md` - Specification refinement
- `tla-review-guidelines.md` - Code review guidelines
- And more...

Resources are accessible via URI: `tlaplus://knowledge/<filename>`

## Troubleshooting

### Java not found

**Error:** `Java executable not found`

**Solutions:**
1. Install Java 11 or higher: https://adoptium.net/
2. Set JAVA_HOME environment variable
3. Use `--java-home /path/to/java` option

### TLA+ tools not found

**Error:** `TLA+ tools jar not found`

**Solutions:**
1. Run `npm run setup` to download TLA+ tools
2. Use `--tools-dir /path/to/tools` to specify the location
3. Verify tla2tools.jar and CommunityModules-deps.jar exist in the tools directory

### Config file not found

**Error:** `No Counter.cfg found`

**Solutions:**
1. Create a .cfg file with the same name as your .tla file
2. Or create MCCounter.tla and MCCounter.cfg files
3. See TLC documentation for config file format

### Permission denied

**Error:** `Access denied: Path is outside the workspace`

**Solution:**
If using `--working-dir`, ensure the file path is within that directory. Otherwise, the server allows access to any file.

## Error Recovery

The server implements comprehensive error recovery with automatic retries for transient failures:

### Automatic Retry Behavior

Transient errors (file locks, Java spawn failures, I/O errors) are automatically retried with exponential backoff:

- **Attempt 1**: Immediate
- **Attempt 2**: After 100ms delay
- **Attempt 3**: After 1s delay
- **Attempt 4**: After 10s delay (max)

Maximum 3 retry attempts before returning error to client.

### Structured Error Codes

All errors include structured error codes for better diagnostics:

```
Error [JAVA_NOT_FOUND]: Java executable not found in "/invalid/path"

Suggested Actions:
- Install Java 17 or later
- Set JAVA_HOME environment variable
- Use --java-home to specify Java location
```

Error codes classify failures as:
- **Transient** - Automatically retried (JAR_LOCKED, JAVA_SPAWN_FAILED, FILE_BUSY)
- **Permanent** - Require user intervention (FILE_NOT_FOUND, JAVA_NOT_FOUND, PARSE_SYNTAX_ERROR)

### Common Error Codes

| Code | Type | Description |
|------|------|-------------|
| `JAVA_NOT_FOUND` | Permanent | Java not installed or misconfigured |
| `JAVA_SPAWN_FAILED` | Transient | Failed to start Java (retried automatically) |
| `FILE_NOT_FOUND` | Permanent | File does not exist |
| `FILE_BUSY` | Transient | File locked by another process |
| `JAR_LOCKED` | Transient | JAR file locked (common on Windows with antivirus) |
| `JAR_ENTRY_NOT_FOUND` | Permanent | Entry not found in JAR archive |
| `CONFIG_TOOLS_NOT_FOUND` | Permanent | TLA+ tools not configured |

See [docs/ERROR-CODES.md](./docs/ERROR-CODES.md) for complete error code reference.

### Verbose Mode

Enable detailed error diagnostics with environment variables:

```bash
VERBOSE=1 tlaplus-mcp-server
# or
DEBUG=1 tlaplus-mcp-server
```

Verbose mode includes:
- Full stack traces for all errors
- Detailed error context (file paths, retry attempts)
- Enhanced debugging information

### Retry Examples

**File lock (Windows antivirus scanning JAR):**
```
Error [JAR_LOCKED]: Cannot access tla2tools.jar

Suggested Actions:
- Close other programs using the JAR file
- Check for antivirus software locking files

Failed after 3 retry attempts.
```

**Java spawn failure (recovered on retry):**
```
# First attempt fails, retried automatically
# Second attempt succeeds - no error shown to user
```

### Graceful Degradation

The server continues operating when non-critical errors occur:

- **Module scanning**: Returns available modules even if some paths fail
- **JAR scanning**: Logs warnings for corrupted JARs but continues
- **Path detection**: Falls back to manual configuration if auto-detection fails

## Architecture

The server is organized into:

- **Tools** (`src/tools/`) - MCP tool implementations (SANY, TLC, knowledge base)
- **Utils** (`src/utils/`) - Core utilities (Java execution, TLA+ tools, parsing)
- **Server** (`src/server.ts`) - MCP server with stdio and HTTP transport
- **CLI** (`src/cli.ts`) - Command-line interface and argument parsing

## Development

```bash
# Install dependencies
npm install

# Build
npm run build

# Watch mode
npm run dev
```

## Testing

The MCP server has comprehensive automated tests covering all utilities and platform-specific code.

```bash
# Run tests
npm test

# Run tests with coverage
npm run test:coverage

# Run in watch mode during development
npm run test:watch
```

### Platform Support

Tested on:
- ✅ macOS (Intel & Apple Silicon)
- ✅ Windows 10/11
- ✅ Linux (Ubuntu, Debian, Fedora)
- ✅ Node.js 18, 20, 22

See [TESTING.md](./TESTING.md) for detailed testing guide.

### Integration Tests

```bash
node test-sany.js         # Basic SANY integration test
node test-fixtures.js     # Comprehensive test with repository fixtures
```

### Test Results

The server has been thoroughly tested with 10 TLA+ specifications from the vscode-tlaplus test suite:

- ✅ 100% test pass rate
- ✅ Valid specifications parse without errors
- ✅ Invalid specifications correctly report errors
- ✅ Tested with real-world TLA+ code

See [TEST-RESULTS.md](./TEST-RESULTS.md) for detailed test results.

## License

MIT

## Contributing

Contributions are welcome! Please open an issue or pull request.

## Related Projects

- [TLA+ Tools](https://github.com/tlaplus/tlaplus) - The TLA+ specification and verification system
- [VSCode TLA+ Extension](https://github.com/tlaplus/vscode-tlaplus) - TLA+ support for Visual Studio Code
- [Model Context Protocol](https://github.com/modelcontextprotocol) - MCP specification and SDKs
