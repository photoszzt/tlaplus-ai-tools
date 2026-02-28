# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

TLA+ AI Tools is a comprehensive Claude Code plugin that integrates TLA+ formal specification and model checking into AI-assisted development workflows. The plugin combines:

- **MCP Server** (`src/`) - TypeScript-based Model Context Protocol server providing TLA+ toolchain access
- **AI Skills** (`skills/`) - Both educational knowledge modules and operational skills (parsing, checking, validating specs)
- **Autonomous Agents** (`agents/`) - Self-directed tasks for validation, config generation, and trace analysis
- **Knowledge Base** (`resources/knowledgebase/`) - 20+ articles on TLA+ best practices and patterns

## Common Commands

### Development

```bash
# Build the MCP server (TypeScript → JavaScript)
npm run build

# Build in watch mode during development
npm run dev

# Download TLA+ tools (tla2tools.jar, CommunityModules-deps.jar)
npm run setup

# Verify installation (checks Java, tools, plugin structure)
npm run verify
```

### Testing

```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Generate coverage report
npm run test:coverage

# Run tests in CI mode
npm run test:ci
```

### Plugin Usage

```bash
# Run Claude Code with this plugin
claude --plugin-dir $(pwd)

# Or install globally and run
npm link
claude

# Verify plugin loaded
/plugin list    # Should show "tlaplus"
```

## Architecture

### MCP Server Architecture (`src/`)

The MCP server is the core integration point that exposes TLA+ tools via the Model Context Protocol:

```
src/
├── index.ts          # Entry point, CLI argument parsing, auto-detection of tool paths
├── server.ts         # MCP server setup (stdio/HTTP modes), tool registration
├── cli.ts            # Command-line argument parser
├── types.ts          # Shared TypeScript types (ServerConfig, etc.)
├── tools/            # MCP tool implementations
│   ├── sany.ts       # SANY parser tools (parse, symbol extraction, module listing)
│   ├── tlc.ts        # TLC model checker tools (check, smoke test, explore)
│   └── knowledge.ts  # Knowledge base resource provider
└── utils/            # Shared utilities
    ├── java.ts       # Java executable detection and validation
    ├── jarfile.ts    # JAR file operations and jarfile:// URI handling
    ├── sany.ts       # SANY parser execution and XML output parsing
    ├── tlc-helpers.ts    # TLC configuration parsing
    ├── symbols/      # Symbol extraction from SANY XML output
    ├── errors/       # Error handling and categorization
    └── paths.ts      # Path resolution and auto-detection
```

**Key Design Patterns:**

1. **Auto-detection**: Paths to Java, TLA+ tools, and knowledge base are auto-detected if not explicitly provided
2. **Dual Transport**: Server supports both stdio (for Claude Code) and HTTP (for remote access)
3. **Error Enhancement**: All errors are categorized with error codes and suggested fixes
4. **JAR URI Support**: Can reference TLA+ modules inside JAR files using `jarfile://path/to/file.jar!/Module.tla`

### Plugin Components

The plugin follows Claude Code's component model:

```
.claude-plugin/
└── plugin.json       # Plugin manifest (name, version, component paths, MCP server config)

skills/               # AI skills (educational + operational)
├── tla-getting-started/  # Educational: TLA+ basics
├── tla-model-checking/   # Educational: Model checking workflow
├── tla-refinement-proofs/ # Educational: Refinement proofs
├── tla-debug-violations/ # Educational: Debugging violations
├── tla-create-animations/ # Educational: Creating animations
├── tla-parse/            # Operational: Parse spec with SANY
├── tla-symbols/          # Operational: Extract symbols and generate config
├── tla-smoke/            # Operational: Quick 3-second smoke test
├── tla-check/            # Operational: Full model checking with TLC
├── tla-review/           # Operational: Comprehensive spec review
└── tla-setup/            # Operational: Interactive setup and verification

agents/               # Autonomous agents (self-directed tasks)
├── animation-creator.md # Create animation specs
└── trace-analyzer.md    # Analyze counterexample traces
```

### MCP Tools Exposed

The server exposes these tools via MCP (prefix: `tlaplus_mcp_`):

**SANY Parser Tools:**

- `sany_parse` - Parse spec, return syntax/semantic errors
- `sany_symbol` - Extract symbols (constants, variables, operators, init/next actions)
- `sany_modules` - List available TLA+ modules in tools JAR

**TLC Model Checker Tools:**

- `tlc_check` - Run exhaustive model checking
- `tlc_smoke` - Run quick random simulation (3-second default)
- `tlc_explore` - Generate specific behavior traces

**Knowledge Base:**

- `knowledge` (resource) - Access 20+ articles on TLA+ best practices

### Component Integration Flow

When a user runs `/tla-check @Counter.tla`:

1. **Skill** (`skills/tla-check/SKILL.md`) is loaded into the main conversation context
2. Skill reads `Counter.tla` using Read tool
3. Skill calls MCP tool `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` to validate syntax
4. If config missing, skill calls `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol` to extract symbols
5. Skill prompts user to generate `Counter.cfg` if needed
6. Skill calls `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check` to run model checking
7. Results are formatted and presented to user

Skills run in the main conversation context where all MCP tools are registered, ensuring reliable tool invocation.

### Hook Behaviors

**SessionStart**: Silently checks if TLA+ tools are installed. Shows notification only if missing.

**PreToolUse (Write/Edit .tla files)**: Auto-parses TLA+ files before saving. Shows warnings but never blocks writes.

**PostToolUse (Write .tla files)**: Suggests running `/tla-symbols` if no `.cfg` file exists for newly created specs.

## Code Style and Conventions

### TypeScript/Node.js Code

- **Error Handling**: All errors are enhanced with error codes via `enhanceError()` from `utils/errors`
- **Path Resolution**: Always use `resolveAndValidatePath()` from `utils/paths` for file paths
- **Java Execution**: Use utilities from `utils/java.ts` - never construct Java commands manually
- **SANY/TLC**: Use high-level wrappers from `utils/sany.ts` and `utils/tlc-helpers.ts`

### Plugin Components (Markdown)

- **Skills (educational)**: Must have YAML frontmatter with `name`, `description`, `version`
- **Skills (operational)**: Must have YAML frontmatter with `name`, `description`, `version`, `allowed-tools`
- **Agents**: Must have YAML frontmatter with `description`, `model`, `color`, `tools`

### Testing

- Tests use Jest with ts-jest
- Test files: `__tests__/*.test.ts` or `*.test.ts`
- Mock utilities in `src/__tests__/helpers/`
- Fixtures in `src/__tests__/fixtures/`

## Dependencies

### Runtime Dependencies

- `@modelcontextprotocol/sdk` - MCP protocol implementation
- `express` - HTTP server for MCP HTTP transport
- `fast-xml-parser` - Parse SANY XML output
- `adm-zip` - Extract modules from JAR files
- `zod` - Runtime schema validation

### External Dependencies

- **Java 11+** - Required to run TLA+ tools (tla2tools.jar)
- **TLA+ Tools** - Downloaded via `npm run setup` to `tools/` directory
  - `tla2tools.jar` - SANY parser and TLC model checker
  - `CommunityModules-deps.jar` - Community modules

### Auto-detection Logic

The server auto-detects paths in this order:

**Java**: `JAVA_HOME` → `java` in PATH → common install locations

**TLA+ Tools**:

1. `tools/` in plugin root
2. `${CLAUDE_PLUGIN_ROOT}/tools/`
3. `~/.tlaplus/tools/`

**Knowledge Base**:

1. `resources/knowledgebase/` in plugin root
2. `${CLAUDE_PLUGIN_ROOT}/resources/knowledgebase/`

## Key Files to Understand

- **`src/server.ts`** - MCP server initialization, tool registration, transport setup
- **`src/tools/sany.ts`** - SANY parser integration, primary interface for validation
- **`src/tools/tlc.ts`** - TLC model checker integration, handles all model checking operations
- **`src/utils/symbols/`** - Symbol extraction from SANY XML (complex XML parsing logic)
- **`.claude-plugin/plugin.json`** - Plugin manifest that Claude Code reads to load components

## TLA+ Toolchain Integration

### SANY Parser

SANY is invoked via `utils/sany.ts`:

```typescript
// Parse spec and get XML output
const result = await runSanyParse(fileName, config);

// Parse XML to extract errors/symbols
const parsed = parseSanyOutput(result.stderr);
```

SANY output is XML. The parser extracts:

- Syntax errors (line/column, message)
- Module dependencies
- Symbol definitions (via separate symbol extraction)

### TLC Model Checker

TLC requires both a `.tla` spec and a `.cfg` config file. The config specifies:

- `SPECIFICATION` or `INIT`/`NEXT`
- `INVARIANT` - properties that should always hold
- `PROPERTY` - temporal properties to check
- `CONSTANT` assignments
- `CONSTRAINT` - state constraints

TLC is invoked via `utils/tlc-helpers.ts` and `tools/tlc.ts`.

### Configuration Files

TLC config files (`.cfg`) are plain text:

```
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT SafetyProperty
CONSTANT MaxValue = 10
```

Generate configs using `/tla-symbols`.

## Common Development Tasks

### Adding a New MCP Tool

1. Add tool implementation in `src/tools/` (sany.ts, tlc.ts, or new file)
2. Register tool in `src/server.ts` via `server.setRequestHandler()`
3. Define input schema with Zod
4. Implement tool handler that returns `{ content: [...], isError?: boolean }`
5. Add error handling with `enhanceError()`
6. Update tests in `src/__tests__/`

### Adding a New Operational Skill

1. Create `skills/skill-name/` directory
2. Add `SKILL.md` with YAML frontmatter (`name`, `description`, `version`, `allowed-tools`)
3. Reference MCP tools using full names (e.g., `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse`)
4. Add "IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash."
5. Write clear implementation steps for Claude to follow
6. Test by running `/skill-name` in Claude Code

### Adding a New Educational Skill

1. Create `skills/skill-name/` directory
2. Add `SKILL.md` with YAML frontmatter (`name`, `description`, `version`)
3. Use progressive disclosure: start with overview, then details
4. Add examples in `examples/` subdirectory if helpful
5. Update skill description to include triggering phrases

### Adding a New Agent

1. Create `agents/agent-name.md` with YAML frontmatter
2. Specify `model` (sonnet/opus/haiku), `color`, `tools`
3. Write clear triggering conditions in description
4. Provide step-by-step execution instructions
5. Test by asking Claude to perform the agent's task

## Troubleshooting

### Java Not Found

Run `/tla-setup` or manually set `JAVA_HOME` environment variable.

### TLA+ Tools Missing

Run `npm run setup` to download tools to `tools/` directory.

### MCP Server Not Starting

Check `npm run build` completed successfully and `dist/index.js` exists.

### Parse Errors Not Showing

SANY outputs errors on stderr. Ensure `parseSanyOutput()` is parsing XML correctly.

### Symbol Extraction Fails

Check `src/utils/symbols/` for XML parsing logic. SANY XML schema is complex.

## Resources

- **TLA+ Homepage**: https://lamport.azurewebsites.net/tla/tla.html
- **Learn TLA+**: https://learntla.com/
- **TLA+ Examples**: https://github.com/tlaplus/Examples
- **VS Code Extension** (reference): https://github.com/tlaplus/vscode-tlaplus
