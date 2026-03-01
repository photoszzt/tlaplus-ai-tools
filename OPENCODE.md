# OpenCode Setup Guide

## Quick Start

```bash
# 1. Build the MCP server
npm run build

# 2. Download TLA+ tools (if not already done)
npm run setup

# 3. Install globally for OpenCode
npm run install-global

# 4. Start OpenCode
opencode
```

**What `npm run install-global` does:**
- Patches `~/.config/opencode/opencode.json` to enable MCP server
- Installs skills to `~/.config/opencode/skills/` (symlink or copy)
- Installs commands to `~/.config/opencode/commands/` (symlink or copy)
- Writes installation marker to prevent repeated prompts
- **Idempotent**: Safe to run multiple times

## What Works in OpenCode

| Component      | Status                    | Notes                                        |
| -------------- | ------------------------- | -------------------------------------------- |
| **MCP Tools**  | ✅ Full Support           | All TLA+ tools accessible via MCP            |
| **Skills (5)** | ✅ Full Support           | All 5 skills discoverable                    |
| **Commands**   | ✅ Supported              | Custom commands via .opencode/commands/\*.md |
| **Agents**     | ⚠️ Different Architecture | Requires oh-my-opencode JSON config          |
| **Hooks**      | ⚠️ Different Architecture | Requires JavaScript plugin files             |

## MCP Tools

The TLA+ MCP server provides these tools in OpenCode:

- `tlaplus_mcp_sany_parse` - Parse and validate TLA+ specifications
- `tlaplus_mcp_tlc_check` - Run exhaustive model checking
- `tlaplus_mcp_tlc_smoke` - Quick random simulation
- `tlaplus_mcp_tlc_explore` - Generate specific behavior traces
- `tlaplus_mcp_sany_symbol` - Extract symbols from specifications
- `tlaplus_mcp_sany_modules` - List available TLA+ modules
- `knowledge` (resource) - Access TLA+ knowledge base

**Verification**:

```bash
opencode mcp list
# Expected output:
# ✓ tlaplus [connected]
#     node ./dist/index.js
```

## Skills

All 5 TLA+ skills are available in OpenCode:

**Learning Skills:**

- `tla-getting-started` - Introduction to TLA+ with examples
- `tla-model-checking` - Complete TLC configuration guide
- `tla-refinement-proofs` - Specification refinement

**Development Skills:**

- `tla-debug-violations` - Debug counterexamples systematically
- `tla-create-animations` - Create SVG animations

**Usage**: Invoke skills with `/skill <name>` in OpenCode chat.

**Verification**:

```bash
opencode debug skill | grep tla-
# Should show all 5 TLA+ skills
```

## Platform Differences

## Commands

OpenCode supports custom commands defined in `.opencode/commands/*.md`. This repository ships 6 TLA+ commands:

- `/tla-parse` - Parse and validate TLA+ specifications
- `/tla-symbols` - Extract symbols and generate TLC configuration
- `/tla-smoke` - Quick 3-second random simulation
- `/tla-check` - Exhaustive model checking
- `/tla-review` - Comprehensive spec review workflow
- `/tla-setup` - Interactive setup and verification

**Usage**: Invoke commands in OpenCode TUI as `/command-name`. Commands accept spec paths as arguments:

```
/tla-parse test-specs/Counter.tla
/tla-symbols test-specs/Counter.tla
/tla-check test-specs/Counter.tla test-specs/Counter.cfg
```

**Note**: If you type `@path/to/spec.tla` as the first argument, the command strips the leading `@` and validates the file exists on disk (MCP tools require filesystem paths).

**Verification**:

```bash
# Commands are auto-discovered from .opencode/commands/
ls .opencode/commands/
# Expected: tla-parse.md tla-symbols.md tla-smoke.md tla-check.md tla-review.md tla-setup.md
```

### Command Format

Commands in this repository use a **unified format** compatible with both Claude Code and OpenCode:

- **Frontmatter**: Contains fields for both platforms
  - `name`, `argument-hint`, `allowed-tools`: Claude Code (ignored by OpenCode)
  - `agent`: OpenCode (ignored by Claude Code)
  - `description`: Shared by both platforms
- **Variables**: All commands use `$ARGUMENTS` for cross-platform compatibility
- **Markers**: Commands output structured markers (e.g., "Spec path:", "CFG used:") for E2E validation

#### Keeping Commands in Sync

The canonical source is `commands/`. OpenCode users should periodically sync:

```bash
cp commands/tla-*.md .opencode/commands/
```

Alternatively, contributors should ensure both directories stay synchronized when updating commands.

### Using Commands from Repo Root

By default, OpenCode loads commands from `.opencode/commands/`. To use commands from the repo root `commands/` directory instead, set the `OPENCODE_CONFIG_DIR` environment variable:

**macOS/Linux**:

```bash
OPENCODE_CONFIG_DIR="$PWD" opencode
```

**Windows (PowerShell)**:

```powershell
$env:OPENCODE_CONFIG_DIR=(Get-Location).Path
opencode
```

This allows you to use the repo's commands without duplicating them into `.opencode/commands/`.

### Agents (Different Architecture)

OpenCode agents are defined in `~/.config/opencode/oh-my-opencode.json` (global JSON config), not as markdown files with frontmatter.

**Claude Code** (this plugin):

```yaml
---
description: Validates TLA+ specifications
model: sonnet
tools:
  - Read
  - Bash
---
```

**OpenCode** (oh-my-opencode):

```json
{
  "agents": {
    "my-agent": {
      "model": "your-model-id"
    }
  }
}
```

The 4 agent files in `agents/` directory are Claude Code-specific and cannot be directly used in OpenCode.

### Hooks (Different Architecture)

OpenCode hooks are JavaScript plugin files in `.opencode/plugins/*.js`, not JSON config with bash scripts.

**Claude Code** (this plugin):

```json
{
  "SessionStart": [
    {
      "type": "prompt",
      "prompt": "Check if TLA+ tools are installed..."
    }
  ]
}
```

**OpenCode** (JavaScript plugin):

```javascript
module.exports = {
  "experimental.chat.system.transform": async (_input, output) => {
    // Hook implementation
  },
};
```

The hooks in `hooks/hooks.json` are Claude Code-specific.

## Configuration

### MCP Server Configuration

The `.opencode/opencode.json` file configures the TLA+ MCP server:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "tlaplus": {
      "type": "local",
      "command": ["node", "./dist/index.js"],
      "enabled": true
    }
  }
}
```

### Custom Tool Paths

If TLA+ tools are in a custom location:

```json
{
  "mcp": {
    "tlaplus": {
      "type": "local",
      "command": [
        "node",
        "./dist/index.js",
        "--tools-dir",
        "/custom/path/to/tools",
        "--kb-dir",
        "/custom/path/to/knowledgebase"
      ],
      "enabled": true
    }
  }
}
```

## Installation Steps

```bash
npm install
npm run build
npm run setup  # Downloads TLA+ tools
npm run install-global  # Installs globally for OpenCode
```

**What gets installed:**
- MCP server config: `~/.config/opencode/opencode.json`
- Skills: `~/.config/opencode/skills/tla-*`
- Commands: `~/.config/opencode/commands/tla-*`
- Marker: `~/.config/opencode/.tlaplus-install-state.json`

**Windows Note**: On Windows, the installer automatically falls back to copying files if symlink creation fails (no admin privileges required).

**Verification:**

```bash
# Check MCP server connection
opencode mcp list
# Expected: ✓ tlaplus [connected]

# Check skills
opencode debug skill | grep tla-
# Expected: All 5 TLA+ skills listed
```

## Migrating from v1.x

If you previously used per-project installation (v1.x), remove the `.opencode/` directory:

```bash
# Remove per-project artifacts (optional)
rm -rf .opencode/

# Install globally
npm run install-global
```

The `.opencode/` directory is no longer used in v2.0+.

## Usage Examples

### Using MCP Tools

In OpenCode chat, you can directly invoke MCP tools:

```
Parse this TLA+ spec using tlaplus_mcp_sany_parse tool with file path test-specs/Counter.tla
```

### Using Skills

```
/skill tla-getting-started
```

The skill will guide you through TLA+ concepts with examples.

### Checking a Specification

```
Use tlaplus_mcp_sany_parse to check test-specs/Counter.tla for syntax errors
```

## Troubleshooting

### Reset Installation State

If you need to reinstall, remove the installation marker:

```bash
rm ~/.config/opencode/.tlaplus-install-state.json
npm run install-global
```

### MCP Server Not Connected

```bash
# Check if server is built
ls dist/index.js

# Rebuild if needed
npm run build

# Check OpenCode config
cat .opencode/opencode.json

# Restart OpenCode
opencode
```

### Skills Not Found

```bash
# Check if skills exist
ls -la skills/

# Verify OpenCode can see them
opencode debug skill | grep tla-
```

### Java Not Found

The TLA+ tools require Java 11+:

```bash
# Check Java installation
java -version

# Install Java if needed (Ubuntu/Debian)
sudo apt-get install openjdk-11-jre

# Or download from https://adoptium.net/
```

## Known Limitations

### Agents Not Portable

The 4 agent files in `agents/` directory use Claude Code's markdown format and cannot be directly used in OpenCode. OpenCode agents are configured in `~/.config/opencode/oh-my-opencode.json`.

### Hooks Not Portable

The hooks in `hooks/hooks.json` use Claude Code's JSON format and cannot be directly used in OpenCode. OpenCode hooks require JavaScript plugin files in `.opencode/plugins/*.js`.

## Comparison: Claude Code vs OpenCode

| Feature             | Claude Code                  | OpenCode                           |
| ------------------- | ---------------------------- | ---------------------------------- |
| **MCP Server**      | ✅ Full                      | ✅ Full                            |
| **Skills**          | ✅ 5 skills                  | ✅ 5 skills                        |
| **Commands**        | ✅ 6 commands                | ✅ 6 commands (.opencode/commands) |
| **Agents**          | ✅ 4 agents                  | ❌ Different format                |
| **Hooks**           | ✅ 3 hooks                   | ❌ Different format                |
| **Knowledge Base**  | ✅ 20+ articles              | ✅ 20+ articles                    |
| **Config Location** | `.claude-plugin/plugin.json` | `.opencode/opencode.json`          |
| **Skills Location** | `skills/`                    | `skills/`                          |

## Support

For issues specific to:

- **TLA+ Tools**: See [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- **This Plugin**: Open an issue on GitHub
- **OpenCode**: See [OpenCode Documentation](https://github.com/sst/opencode)

## See Also

- [CLAUDE.md](CLAUDE.md) - Claude Code setup guide
- [README.md](README.md) - General plugin documentation
- [TESTING.md](TESTING.md) - Testing procedures
