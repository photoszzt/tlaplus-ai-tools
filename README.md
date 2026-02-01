# TLA+ AI Tools

> Complete TLA+ formal specification and model checking toolkit for Claude Code and OpenCode

**AI-powered assistance for writing, verifying, and debugging TLA+ specifications.**

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Node Version](https://img.shields.io/badge/node-%3E%3D18.0.0-brightgreen)](https://nodejs.org/)
[![Java Version](https://img.shields.io/badge/java-%3E%3D11-orange)](https://adoptium.net/)

## Overview

TLA+ AI Tools is a comprehensive plugin that brings the power of TLA+ formal methods to AI coding assistants. It combines an MCP server for TLA+ tools with AI skills, commands, agents, and hooks to provide intelligent assistance throughout the entire TLA+ workflow.

**Key Capabilities:**

- 🤖 **AI Skills** - Learn TLA+, model checking, refinement, and debugging
- ⚡ **Slash Commands** - Parse, check, smoke test, review, and more
- 🎯 **Autonomous Agents** - Automated validation, config generation, trace analysis
- 🔗 **Event Hooks** - Auto-parse on save, suggest configs, verify tools
- 🛠️ **MCP Integration** - Full access to SANY parser and TLC model checker
- 📚 **Knowledge Base** - 20+ articles on TLA+ best practices

## Features

### AI Skills (6)

**For Learning:**

- **tla-getting-started** - Introduction to TLA+ with examples and tutorials
- **tla-model-checking** - Complete guide to TLC configuration and workflows
- **tla-refinement-proofs** - Specification refinement and verification

**For Development:**

- **tla-spec-review** - Comprehensive specification review checklist
- **tla-debug-violations** - Systematic debugging of counterexamples
- **tla-create-animations** - Visualize specifications with SVG animations

### Slash Commands (6)

- `/tla-parse` - Parse and validate TLA+ specifications
- `/tla-check` - Run exhaustive model checking with TLC
- `/tla-smoke` - Quick 3-second smoke test
- `/tla-symbols` - Extract symbols and generate TLC config
- `/tla-review` - Comprehensive spec review with validation
- `/tla-setup` - Interactive setup and verification

### Autonomous Agents (4)

- **spec-validator** - Automatically validate specifications
- **config-generator** - Generate TLC configuration files
- **animation-creator** - Create visualization animations
- **trace-analyzer** - Analyze and explain counterexamples

### Event Hooks (3)

- **SessionStart** - Verify TLA+ tools on startup
- **PreToolUse** - Auto-parse TLA+ files before saving
- **PostToolUse** - Suggest config generation for new specs

### MCP Tools

Full integration with TLA+ toolchain:

- **SANY Parser** - Syntax and semantic validation
- **TLC Model Checker** - Exhaustive state space exploration
- **Smoke Testing** - Fast random simulation
- **Behavior Exploration** - Generate execution traces
- **Symbol Extraction** - Analyze spec structure
- **Knowledge Base** - Access TLA+ documentation

## Installation

### Quick Start (Recommended)

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
cc --plugin-dir $(pwd)
```

### From npm (Coming Soon)

```bash
npm install -g tlaplus-ai-tools
cc
```

### Claude Code Marketplace (Coming Soon)

```
/plugin install tlaplus
```

### OpenCode

```bash
# Build and start
npm run build
opencode

# Verify MCP connection
opencode mcp list
```

See [OPENCODE.md](OPENCODE.md) for detailed OpenCode setup and platform differences.

See [INSTALLATION.md](INSTALLATION.md) for detailed instructions.

## Requirements

- **Node.js** 18.0.0 or higher
- **Java** 11 or higher (for TLA+ tools)
- **Claude Code** or **OpenCode**

## Quick Start Guide

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
2. Auto-parse on save (hook)
3. /tla-symbols to generate config
4. /tla-smoke for quick test
5. /tla-check for full verification
```

### Debugging Violations

```
1. TLC reports violation
2. Use trace-analyzer agent
3. Understand counterexample
4. Fix based on suggestions
5. Re-run /tla-check
```

### Creating Animations

```
1. Ask: "create animation for my spec"
2. animation-creator agent generates anim spec
3. /tla-check @SpecAnim.tla
4. View animated state transitions
```

## Documentation

- **[INSTALLATION.md](INSTALLATION.md)** - Complete installation guide
- **[TESTING.md](TESTING.md)** - Testing and verification guide
- **[CHANGELOG.md](CHANGELOG.md)** - Version history and changes
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Contribution guidelines (coming soon)

## Development

### Running Tests

Install development dependencies:

```bash
python3 -m pip install -r requirements-dev.txt
```

Run tests:

```bash
# Unit tests (when available)
pytest
```

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
hooks:
  autoParseOnSave: true
  suggestConfigGeneration: true
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
├── skills/          # AI skills for TLA+ knowledge
├── commands/        # Slash commands for user actions
├── agents/          # Autonomous agents for automation
├── hooks/           # Event-driven automation
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
- ✅ **OpenCode**

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

### Plugin Not Loading

```bash
# Verify structure
npm run verify

# Try explicit path
cc --plugin-dir $(pwd)

# Check plugin list
/plugin list
```

See [INSTALLATION.md](INSTALLATION.md) for more troubleshooting.

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

- [Installation Guide](INSTALLATION.md)
- [Testing Guide](TESTING.md)
- [Changelog](CHANGELOG.md)
- [License](LICENSE)

---

**Made with ❤️ for the TLA+ community**

Start formally verifying your systems today! 🚀
