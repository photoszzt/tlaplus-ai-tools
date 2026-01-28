# OpenCode Support Learnings

## OpenCode Component Discovery (2026-01-28)

### MCP Server Loading
- **Location**: `.opencode/opencode.json` (project-level)
- **Format**: JSON with "mcp" key containing server definitions
- **Example**:
  ```json
  {
    "mcp": {
      "tlaplus": {
        "type": "local",
        "command": ["node", "./dist/index.js"],
        "enabled": true
      }
    }
  }
  ```
- **Verification**: `opencode mcp list` shows connected servers
- **Status**: ✅ Working (tlaplus server connected)

### Skills Loading
- **Location**: `~/.config/opencode/skills/` (global, via symlinks)
- **Format**: Directory with SKILL.md file (same as Claude Code)
- **Discovery**: OpenCode's native `skill` tool
- **Pattern**: Symlinks from global skills dir to actual skill directories
- **Example**: `~/.config/opencode/skills/brainstorming -> ../superpowers/skills/brainstorming`
- **Status**: ✅ Working (superpowers skills loaded)

### Agents Configuration
- **Location**: `~/.config/opencode/oh-my-opencode.json` (global)
- **Format**: JSON with "agents" key (NOT markdown files)
- **Required Fields**: `model` (e.g., "inference-nvidia-claude/aws/anthropic/claude-opus-4-5")
- **Optional Fields**: `variant` (e.g., "high", "max")
- **Key Difference**: OpenCode agents are JSON-configured, not markdown-based like Claude Code
- **Status**: ✅ Working (7 agents configured: build, explore, plan, etc.)

### Hooks Implementation
- **Location**: `.opencode/plugins/*.js` (JavaScript plugin files)
- **Format**: JavaScript exports with hook handlers
- **Example**: `experimental.chat.system.transform` hook in superpowers.js
- **Key Difference**: Hooks are JS functions, not JSON config + bash scripts like Claude Code
- **Status**: ✅ Working (superpowers plugin uses system prompt transform)

### Commands Support
- **Status**: ❌ Not supported in OpenCode
- **Note**: OpenCode does not have a `/command-name` slash command system like Claude Code
- **Alternative**: Use built-in commands (mcp, agent, debug) or custom plugins

### Key Architectural Differences from Claude Code

1. **Plugin Directory**: `.opencode/` instead of `.claude-plugin/`
2. **Agent System**: JSON-configured agents (oh-my-opencode framework) vs markdown-based agents
3. **Hook System**: JavaScript plugin files vs JSON config + bash scripts
4. **Skills**: Global symlinks vs project-level directories
5. **Commands**: Not supported vs core feature

### Recommended Plugin Structure for OpenCode

```
tlaplus-ai-tools/
├── .opencode/
│   ├── opencode.json          # MCP server config
│   └── plugins/               # Optional: JS hook implementations
│       └── tlaplus.js
├── skills/                     # To be symlinked to ~/.config/opencode/skills/
│   ├── tla-getting-started/
│   ├── tla-model-checking/
│   └── ...
├── dist/
│   └── index.js               # MCP server
└── README.md
```

### Installation Process for OpenCode

1. Build MCP server: `npm run build`
2. Configure MCP: Create `.opencode/opencode.json` with server config
3. Install skills: Symlink skill directories to `~/.config/opencode/skills/tla-*`
4. Verify: `opencode mcp list` to confirm server connection

### Testing Commands

```bash
# Check MCP status
opencode mcp list

# Check agent configuration
opencode agent list

# Debug configuration
opencode debug config

# Check skills (may fail with error, but skills still work)
opencode debug skill
```

## Task 7: Commands Testing (2026-01-28)

### Finding: Commands Not Supported in OpenCode

**Test Results:**
- Tested all 6 TLA+ commands: `/tla-parse`, `/tla-smoke`, `/tla-symbols`, `/tla-check`, `/tla-review`, `/tla-setup`
- **Result**: NONE work - OpenCode has no slash command system

**Evidence:**
1. `opencode --help` shows CLI commands (mcp, agent, debug) but no slash command extension mechanism
2. No `/command-name` invocation syntax exists in OpenCode
3. Superpowers plugin does not register any commands
4. No command-related config files or directories in `~/.config/opencode/`

**Architectural Difference:**
- Claude Code: Supports slash commands as plugin components (`.claude-plugin/commands/`)
- OpenCode: No slash command system - uses different extension model

**Decision:**
- `commandsSupported = NO`
- `task8Needed = NO` (commands cannot be ported without architectural changes)

**Alternative Approaches for OpenCode:**
1. **MCP Tools** - Already working, provides programmatic access to TLA+ tools
2. **Skills** - Can guide users through workflows (e.g., "parse this spec")
3. **Chat Integration** - Users can ask "parse Counter.tla" instead of `/tla-parse @Counter.tla`

**Recommendation:**
Skip Task 8 (command porting). Focus on:
- Skills (already working via symlinks)
- MCP tools (already working)
- Documentation updates to reflect OpenCode's different interaction model


## Skills Discovery in OpenCode (2026-01-28)

### Key Finding
OpenCode discovers skills from `.claude/skills/` directory (project-level), NOT from `skills/` directory specified in `.claude-plugin/plugin.json`.

### Evidence
- Tested all 6 TLA+ skills using `opencode debug skill`
- Only 3 skills detected (all from `.claude/skills/`)
- 3 skills missing (in `skills/` but not in `.claude/skills/`)
- Claude Code uses `skills/` per `.claude-plugin/plugin.json`
- OpenCode ignores `.claude-plugin/plugin.json` skills path

### Skills Status
**Accessible (3):**
- tla-spec-review
- tla-debug-violations
- tla-create-animations

**Missing (3):**
- tla-getting-started
- tla-model-checking
- tla-refinement-proofs

### Decision
Copy 3 missing skills from `skills/` to `.claude/skills/` to make them accessible in OpenCode.

### Pattern
OpenCode uses `.claude/` directory for project-level components:
- `.claude/skills/` - Skills (discovered by OpenCode)
- `.opencode/opencode.json` - MCP server config (OpenCode-specific)
- `.claude-plugin/plugin.json` - Claude Code config (ignored by OpenCode)

### Architectural Difference
- **Claude Code**: Uses `.claude-plugin/plugin.json` to specify skills path
- **OpenCode**: Directly discovers skills from `.claude/skills/` directory

## Task 5 Completion - Skill Directory Sync (2026-01-27)

Successfully copied 3 missing skills from skills/ to .claude/skills/:
- tla-getting-started/
- tla-model-checking/
- tla-refinement-proofs/

Verification: All diff -r checks passed (no output = identical copies)

Result: .claude/skills/ now contains all 6 TLA+ skills, matching the source skills/ directory.

