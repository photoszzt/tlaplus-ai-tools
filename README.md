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
- **tlc_trace** - Replay saved TLC counterexample traces with ALIAS expressions

**Animation Tools (3):**

- **animation_detect** - Detect animation elements in specs
- **animation_render** - Render animation frames as SVG
- **animation_frameCount** - Count animation frames

## Installation

### Claude Code Plugin Installation

**Via Plugin Marketplace (Automatic):**

```bash
# Add to marketplace
claude plugin marketplace add https://gitlab-master.nvidia.com/zhitingz/tlaplus-ai-tools.git
claude plugin install tlaplus
```

**Note:** The plugin now includes automatic setup during installation. The MCP server is built and TLA+ tools are downloaded automatically when you install the plugin.

### Codex Plugin Installation

```bash
codex plugin marketplace add https://gitlab-master.nvidia.com/zhitingz/tlaplus-ai-tools.git
codex plugin add tlaplus@tlaplus
```

No local build is required. On first startup, the installed plugin downloads its
runtime dependencies and TLA+ JARs automatically, then runs the shared TypeScript
MCP server through `tsx`. Later startups reuse those files. Node.js, npm, Java,
and network access are needed for initial setup. The Codex skills are maintained
in [`codex/tlaplus/skills/`](codex/tlaplus/skills/). See the
[Codex plugin notes](codex/tlaplus/README.md) for updates and migration from the
previous `tlaplus-local` installation.

### Local install

```bash
# Clone repository
git clone https://gitlab-master.nvidia.com/zhitingz/tlaplus-ai-tools.git
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

### Local HTTP Transport

Run `node dist/index.js --http --port 3000` to serve MCP at
`http://127.0.0.1:3000/mcp`. HTTP mode binds to loopback and accepts only
loopback Host headers. Clients can omit Origin; when present, it must match
the server's HTTP origin using `localhost`, `127.0.0.1`, or `[::1]` and its port.
Foreign or opaque Origins receive HTTP 403 before the request body is parsed.

Remote access requires a tunnel or a local authenticated proxy. A proxy must
forward a loopback Host header and enforce its own browser Origin policy.

Add `--http-session` to enable persistent MCP sessions, GET event streams, and
DELETE session termination. This mode supports subscriptions and client
elicitation/sampling. The default HTTP mode remains stateless. Session mode
allows 32 concurrent sessions and expires sessions after 30 minutes without
activity when no POST request is active. Session termination cancels pending
tool requests and releases connection resources. Sessions do not survive a
server restart.

### Workflows, Resources, and Client Interactions

MCP clients can list/get prompts named after the maintained skills, such as
`tla-check`, `tla-review`, and `tla-create-animations`. Optional `fileName` and
`cfgFile` arguments offer completion for files in the configured working
directory. Prompt messages include the workflow instructions and use the
registered MCP tool names. Supporting files are available through
`tlaplus://skills/{skill}/{file}`; URL-encode relative paths containing slashes.
The shared config-selection instructions are at
`tlaplus://skills/shared/cfg-selection-algorithm.md`.

Knowledge resources also support `tlaplus://knowledge/{article}` with article
name completion. Stdio and session HTTP clients can subscribe to article
changes. Reads use the refreshed catalog, and notifications identify changed
URIs without sending article contents. Adding/removing articles changes the
resource list. Default stateless HTTP uses the startup knowledge snapshot and
does not advertise subscriptions.

Use `tlaplus_mcp_animation_render` with `protocol: "mcp"` for a PNG image and
frame metadata, plus an embedded SVG when its content is inert. PNG and SVG
resources use `tlaplus://animation/{frameId}/{format}`, with `frame.png` or
`frame.svg` as the format. Stdio/session HTTP retains the latest eight frames
on that connection; another connection cannot read them. Stateless HTTP returns
the image and SVG inline without retaining downloadable resources. Native
rendering uses the existing optional canvas package and rejects oversized
images or non-regular file sources. Unsafe SVG content is omitted from SVG
responses; its supported shapes can still produce a PNG.

`tlaplus_mcp_tlc_prepare_config` returns a draft from `init`, `next`, and
`invariants`. It does not write files or run TLC. Set `askUser: true` to request
run mode, worker count, deadlock checking, and invariant selection through a
non-sensitive form with defaults and titled choices. The client must support
form elicitation. Decline/cancel stops preparation.

Set `useSampling: true` and provide `specText` to request model advice from a
client that supports sampling. Only that supplied text is sent; project files
and other client context are not added. Advice is returned separately as an
unverified suggestion, and never applied to the draft automatically. Validate
and complete constant assignments before checking the spec. Audio remains a
test fixture because the tools do not have an audio workflow.

### TLC Progress and Logging

TLC tools stream native progress/statistics messages while Java runs. Request
progress with `_meta.progressToken`; integer `0` and empty-string tokens are
supported. Progress counts updates and omits `total`, because TLC discovers
the state space during execution. The message carries generated/distinct state
counts, queue size, search depth or simulation trace count, and available rates.
Simulation and DFID can report `-1` for unavailable statistics.
No percentage or ETA is inferred.

Progress reports use a five-second TLC interval unless `extraJavaOpts` supplies
`-Dtlc2.TLC.progressInterval=<seconds>`. Lifecycle and final-status updates also
arrive for short runs. Notifications are rate-limited and buffered in a bounded
queue; the latest statistics are retained during bursts.

The server supports `logging/setLevel` and sends safe TLC lifecycle/statistics
through `notifications/message`. Model state dumps and arbitrary `PrintT`
output remain in the tool result. Stdio/session HTTP logging levels apply to
each connection; the stateless HTTP endpoint shares one minimum level across
clients.

### Conformance Testing

From a development checkout, run `npm run setup`, then
`npm run test:conformance`. The command uses the pinned MCP conformance revision
`c37eec888e1c6ff140af79987a40008548b7cc5f` against MCP `2025-11-25` and writes
reports under `conformance-results/`.

Application results and fixture results are separate. The application baseline
records 20 prescribed-fixture failures and the
unexercised optional session-ID gate; a baseline pass
does not claim complete SDK conformance. Session-mode production reports appear
under `application-sessions/` and exercise the session gate. The test-only fixture server reuses
production tool/resource registration, HTTP guards, and the live TLC wrapper,
then adds the required `test_*` tools, prompts, resources, and interactive
fixtures. Its active suite runs with no expected failures. Production does not
register fixture capabilities. The npm package excludes fixture files; Git
installations contain the test sources without activating them.

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
├── .codex-plugin/   # Codex manifest for Git marketplace installation
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

Run `codex plugin list --json` and check for an enabled `tlaplus@tlaplus`
entry. First startup installs the cached runtime's dependencies and missing JARs.
If setup fails, read the MCP startup diagnostic, fix the reported Java, npm, or
network problem, and restart the server. Use `$tla-setup` to verify Java, JARs,
the MCP connection, and a SANY parse. See the
[Codex plugin notes](codex/tlaplus/README.md) for recovery instructions.

## Contributing

### Maintenance

Run `python3 scripts/sync_upstream.py --dry-run` to preview imported knowledge
updates, then `python3 scripts/sync_upstream.py` to merge them and refresh the
published TLA+ JARs. Use `--docs-only` or `--jars-only` for one component, and
`--upstream /path/to/vscode-tlaplus` to read a local upstream clone. Install dev
dependencies first with `npm ci` and commit knowledge-base edits before applying.
The upstream currently publishes knowledge articles, not plugin skills; local
skills remain maintained here and read the updated guidance. Conflicts stop the
doc update without writing articles or advancing its recorded revision.

`resources/knowledgebase/.upstream-revision` records the last imported upstream
snapshot. Its initial baseline is the last knowledge-base commit before our
February 27, 2026 manual sync. After publishing source changes, refresh the
Codex marketplace with `codex plugin marketplace upgrade tlaplus`, reinstall
`tlaplus@tlaplus`, and start a new task.

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
