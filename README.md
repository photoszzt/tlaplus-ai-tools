# TLA+ AI Tools

> TLA+ formal specification and model checking toolkit for Claude Code and Codex

**AI-powered assistance for writing, verifying, and debugging TLA+ specifications.**

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Node Version](https://img.shields.io/badge/node-%3E%3D18.14.0-brightgreen)](https://nodejs.org/)
[![Java Version](https://img.shields.io/badge/java-%3E%3D11-orange)](https://adoptium.net/)

## Overview

TLA+ AI Tools is a comprehensive plugin that brings the power of TLA+ formal methods to AI coding assistants. It combines an MCP server for TLA+ tools with AI skills to provide intelligent assistance throughout the entire TLA+ workflow.

**Key Capabilities:**

- 🤖 **AI Skills** - Learn TLA+, model checking, refinement, debugging, and animation creation
- 🛠️ **MCP Integration** - Full access to SANY parser, TLC model checker, and animation tools
- 📚 **Knowledge Base** - 20+ articles on TLA+ best practices

## Features

### AI Skills (12)

**Educational (5):**

- **tla-getting-started** - Introduction to TLA+ with examples and tutorials
- **tla-model-checking** - Complete guide to TLC configuration and workflows
- **tla-refinement-proofs** - Specification refinement and verification
- **tla-debug-violations** - Systematic debugging of counterexamples
- **tla-create-animations** - Visualize specifications with SVG animations

**Operational (7):**

- **tla-parse** - Parse and validate TLA+ specifications
- **tla-check** - Run exhaustive model checking with TLC
- **tla-smoke** - Quick 3-second smoke test
- **tla-explore** - Generate behavior traces with TLC
- **tla-symbols** - Extract symbols and generate TLC config
- **tla-review** - Comprehensive spec review with validation
- **tla-setup** - Interactive setup and verification

### MCP Tools (10)

Full integration with TLA+ toolchain:

**SANY Parser Tools (3):**

- **sany_parse** - Syntax and semantic validation
- **sany_symbol** - Analyze spec structure and extract symbols
- **sany_modules** - List available TLA+ modules

**TLC Model Checker Tools (4):**

- **tlc_check** - Exhaustive state space exploration
- **tlc_smoke** - Fast random simulation
- **tlc_explore** - Generate execution traces
- **tlc_trace** - Parse and analyze TLC counterexample traces

**Animation Tools (3):**

- **animation_detect** - Detect animation elements in specs
- **animation_render** - Render animation frames as SVG
- **animation_frameCount** - Count animation frames

## Installation

### Claude Code Plugin Installation

**Via Plugin Marketplace (Automatic):**

```bash
# Add to marketplace
claude plugin marketplace add https://github.com/photoszzt/tlaplus-ai-tools.git
claude plugin install tlaplus
```

**Note:** The plugin now includes automatic setup during installation. The MCP server is built and TLA+ tools are downloaded automatically when you install the plugin.

### Codex Plugin Installation (local repository)

Codex supports Git-backed marketplaces, but this repository currently requires a
local build: the marketplace points to the gitignored `plugins/tlaplus` directory,
which bundles the compiled MCP server, TLA+ JARs, and runtime dependencies.
Register a local clone after building it; adding only the repository URL does not
produce that plugin bundle.

```bash
pnpm install
pnpm run build
pnpm run setup
python3 scripts/build_codex_plugin.py
codex plugin marketplace add "$(pwd)"
codex plugin add tlaplus@tlaplus-local
```

The Codex skills are maintained in [`codex/tlaplus/skills/`](codex/tlaplus/skills/),
while the MCP server implementation is shared with the Claude Code plugin. The
plugin build installs its runtime dependencies with pnpm before registration;
pass `--package-manager bun` to use Bun instead. Start
a new Codex task after installation to load the skills and tools. See the
[Codex plugin notes](codex/tlaplus/README.md) for rebuild and recovery details.

### Local install

```bash
# Clone repository
git clone https://github.com/photoszzt/tlaplus-ai-tools.git
cd tlaplus-ai-tools

# Install and setup
npm install
npm run build
npm run setup    # Downloads TLA+ tools

# Verify installation
npm run verify

# Use with Claude Code
claude --plugin-dir $(pwd)
```

## Requirements

- **Node.js** 18.14.0 or higher
- **Java** 11 or higher (for TLA+ tools)
- **Claude Code or Codex**

## Quick Start Guide (Claude Code)

### 1. Create Your First Spec

```
User: "I want to learn TLA+"
→ tla-getting-started skill loads with tutorial
```

Follow the guidance to create a simple counter specification.

### 2. Generate Configuration

```
/tla-symbols @Counter.tla
→ Generates Counter.cfg with proper settings
```

### 3. Test Quickly

```
/tla-smoke @Counter.tla
→ 3-second smoke test finds obvious bugs
```

### 4. Full Verification

```
/tla-check @Counter.tla
→ Exhaustive model checking
```

### 5. Review and Debug

```
/tla-review @Counter.tla
→ Comprehensive review with automated validation
```

## Workflows

### Learning TLA+

```
1. Ask: "teach me TLA+"
2. Follow tla-getting-started skill
3. Create example specs
4. Run /tla-parse and /tla-smoke
5. Progress to /tla-check
```

### Writing Specifications

```
1. Write spec in editor
2. /tla-symbols to generate config
3. /tla-smoke for quick test
4. /tla-check for full verification
```

### Debugging Violations

```
1. TLC reports violation
2. Use /tla-debug-violations skill
3. Understand counterexample
4. Fix based on suggestions
5. Re-run /tla-check
```

### Creating Animations

```
1. Ask: "create animation for my spec"
2. /tla-create-animations skill generates anim spec
3. /tla-check @SpecAnim.tla
4. View animated state transitions
```

## Documentation

- **[TESTING.md](TESTING.md)** - Testing and verification guide
- **[CHANGELOG.md](CHANGELOG.md)** - Version history and changes
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Contribution guidelines (coming soon)

## Configuration

### Custom Settings (Optional)

Create `.claude/tlaplus.local.md` in your project:

```yaml
---
javaHome: /usr/lib/jvm/java-17
toolsDir: /custom/path/to/tools
tlcDefaults:
  workers: 8
  heapSize: 8192
---
```

All settings are optional - the plugin auto-detects paths by default.

## Examples

### Counter Specification

```tla
---- MODULE Counter ----
EXTENDS Naturals

CONSTANT MaxValue
VARIABLE count

Init == count = 0

Increment == count < MaxValue /\ count' = count + 1
ReachMax  == count = MaxValue /\ count' = count

Next == Increment \/ ReachMax

Spec == Init /\ [][Next]_<<count>>

TypeInvariant == count \in 0..MaxValue
BoundInvariant == count <= MaxValue
====
```

### Usage

```
/tla-parse @Counter.tla         # Validate syntax
/tla-symbols @Counter.tla        # Generate Counter.cfg
/tla-smoke @Counter.tla          # Quick test (3s)
/tla-check @Counter.tla          # Full verification
```

More examples in `skills/*/examples/` directories.

## Architecture

```
tlaplus-ai-tools/
├── skills/          # AI skills (educational + operational)
├── codex/tlaplus/   # Codex-specific skills and plugin manifest
├── plugins/tlaplus/ # Generated local Codex plugin (gitignored)
├── src/             # MCP server source code
├── dist/            # Compiled MCP server
├── tools/           # TLA+ tools (downloaded)
└── resources/       # Knowledge base articles
```

## Platform Support

- ✅ **macOS** (Intel & Apple Silicon)
- ✅ **Linux** (Ubuntu, Debian, Fedora)
- ✅ **Windows** 10/11 (via WSL for scripts)
- ✅ **Claude Code**
- ✅ **Codex**

## Troubleshooting

### Java Not Found

```bash
# Install Java 11+
# macOS: brew install openjdk@17
# Linux: sudo apt-get install openjdk-17-jdk
# Windows: https://adoptium.net/

# Verify
java -version
```

### TLA+ Tools Missing

```bash
# Download tools
npm run setup

# Verify
npm run verify
```

### Claude Code Plugin Not Loading

```bash
# Verify structure
npm run verify

# Try explicit path
claude --plugin-dir $(pwd)

# Check plugin list
/plugin list
```

### Codex Plugin Not Loading

Run `codex plugin list --json` and check for an enabled `tlaplus@tlaplus-local`
entry whose source is this repository's `plugins/tlaplus` directory. Check
`plugins/tlaplus/.mcp.json` for its startup path. If the build or bundled JARs
are missing, run `pnpm run build`, `pnpm run setup`, and
`python3 scripts/build_codex_plugin.py` from the repository root. Reinstall the
Codex plugin and start a new task so its tools can load. The `$tla-setup` skill
runs a Java, JAR, MCP connection, and SANY parse check.

## Contributing

Contributions are welcome! This project is derived from and inspired by [vscode-tlaplus](https://github.com/tlaplus/vscode-tlaplus).

Please:

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests if applicable
5. Submit a pull request

## License

MIT License - see [LICENSE](LICENSE) file for details.

## Acknowledgments

- **TLA+ Tools** - [tlaplus/tlaplus](https://github.com/tlaplus/tlaplus)
- **VS Code Extension** - [tlaplus/vscode-tlaplus](https://github.com/tlaplus/vscode-tlaplus)
- **Model Context Protocol** - [modelcontextprotocol](https://github.com/modelcontextprotocol)
- **Leslie Lamport** - Creator of TLA+

## Related Projects

- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Examples](https://github.com/tlaplus/Examples)
- [TLA+ Google Group](https://groups.google.com/g/tlaplus)

## Support

- **Issues**: [GitHub Issues](https://github.com/photoszzt/tlaplus-ai-tools/issues)
- **Discussions**: [GitHub Discussions](https://github.com/photoszzt/tlaplus-ai-tools/discussions)
- **TLA+ Help**: [TLA+ Google Group](https://groups.google.com/g/tlaplus)

## Status

- ✅ **Development**: Complete
- ✅ **Testing**: Structure validated
- ⏳ **Marketplace**: Ready for submission
- ✅ **Open Source**: Available now

## Quick Links

- [Testing Guide](TESTING.md)
- [Changelog](CHANGELOG.md)
- [License](LICENSE)

---

**Made with ❤️ for the TLA+ community**

Start formally verifying your systems today! 🚀
