# OpenCode Setup Guide

## Quick Start

```bash
# 1. Build the MCP server
npm run build

# 2. Start OpenCode (auto-detects .opencode/opencode.json)
opencode
```

OpenCode will automatically load the TLA+ MCP server from `.opencode/opencode.json`.

## What Works in OpenCode

| Component | Status | Notes |
|-----------|--------|-------|
| **MCP Tools** | ✅ Full Support | All TLA+ tools accessible via MCP |
| **Skills (6)** | ✅ Full Support | All 6 skills discoverable |
| **Commands** | ✅ Supported | Custom commands via .opencode/commands/*.md |
| **Agents** | ⚠️ Different Architecture | Requires oh-my-opencode JSON config |
| **Hooks** | ⚠️ Different Architecture | Requires JavaScript plugin files |

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

All 6 TLA+ skills are available in OpenCode:

**Learning Skills:**
- `tla-getting-started` - Introduction to TLA+ with examples
- `tla-model-checking` - Complete TLC configuration guide
- `tla-refinement-proofs` - Specification refinement

**Development Skills:**
- `tla-spec-review` - Comprehensive spec review checklist
- `tla-debug-violations` - Debug counterexamples systematically
- `tla-create-animations` - Create SVG animations

**Usage**: Invoke skills with `/skill <name>` in OpenCode chat.

**Verification**:
```bash
opencode debug skill | grep tla-
# Should show all 6 TLA+ skills
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
  "SessionStart": [{
    "type": "prompt",
    "prompt": "Check if TLA+ tools are installed..."
  }]
}
```

**OpenCode** (JavaScript plugin):
```javascript
module.exports = {
  'experimental.chat.system.transform': async (_input, output) => {
    // Hook implementation
  }
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

### 1. Build the MCP Server

```bash
npm install
npm run build
npm run setup  # Downloads TLA+ tools
```

### 2. Verify MCP Server

```bash
# Check that dist/index.js was created
ls -la dist/index.js

# Test the server
node dist/index.js --help
```

### 3. Configure OpenCode

The `.opencode/opencode.json` file is already included in this repository. OpenCode will auto-detect it when you run `opencode` from the repo root.

### 4. Install Skills (Optional)

Skills are automatically discovered from `.claude/skills/` directory. For global access across all projects, create symlinks:

```bash
# Create symlinks in global skills directory
mkdir -p ~/.config/opencode/skills
ln -s $(pwd)/.claude/skills/tla-getting-started ~/.config/opencode/skills/
ln -s $(pwd)/.claude/skills/tla-model-checking ~/.config/opencode/skills/
ln -s $(pwd)/.claude/skills/tla-refinement-proofs ~/.config/opencode/skills/
ln -s $(pwd)/.claude/skills/tla-spec-review ~/.config/opencode/skills/
ln -s $(pwd)/.claude/skills/tla-debug-violations ~/.config/opencode/skills/
ln -s $(pwd)/.claude/skills/tla-create-animations ~/.config/opencode/skills/
```

### 5. Start OpenCode

```bash
cd /path/to/tlaplus-ai-tools
opencode
```

### 6. Verify Installation

```bash
# Check MCP server connection
opencode mcp list
# Expected: ✓ tlaplus [connected]

# Check skills
opencode debug skill | grep tla-
# Expected: All 6 TLA+ skills listed
```

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
ls -la .claude/skills/

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

| Feature | Claude Code | OpenCode |
|---------|-------------|----------|
| **MCP Server** | ✅ Full | ✅ Full |
| **Skills** | ✅ 6 skills | ✅ 6 skills |
| **Commands** | ✅ 6 commands | ✅ 6 commands (.opencode/commands) |
| **Agents** | ✅ 4 agents | ❌ Different format |
| **Hooks** | ✅ 3 hooks | ❌ Different format |
| **Knowledge Base** | ✅ 20+ articles | ✅ 20+ articles |
| **Config Location** | `.claude-plugin/plugin.json` | `.opencode/opencode.json` |
| **Skills Location** | `skills/` | `.claude/skills/` |

## Support

For issues specific to:
- **TLA+ Tools**: See [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- **This Plugin**: Open an issue on GitHub
- **OpenCode**: See [OpenCode Documentation](https://github.com/sst/opencode)

## See Also

- [CLAUDE.md](CLAUDE.md) - Claude Code setup guide
- [README.md](README.md) - General plugin documentation
- [TESTING.md](TESTING.md) - Testing procedures
