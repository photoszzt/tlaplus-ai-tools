# Add OpenCode Support to TLA+ AI Tools Plugin

## TL;DR

> **Quick Summary**: Add OpenCode platform support while preserving all Claude Code functionality. This is a **discovery-first plan** where Wave 2 validates OpenCode behavior before implementation.
> 
> **Deliverables**:
> - `.opencode/opencode.json` - OpenCode configuration
> - `.opencode/skills/**/*` - Skills for OpenCode (count determined by Task 4)
> - `.opencode/agents/*.md` - 4 agents in OpenCode format (format determined by Task 2)
> - `hooks/prompts.json` - Shared hook prompts (verbatim from hooks.json)
> - `OPENCODE.md` - Setup guide with validated platform differences
> 
> **Estimated Effort**: Medium
> **Parallel Execution**: YES - 3 waves

---

## Context

### Original Request
Add OpenCode support to the TLA+ AI Tools plugin without breaking existing Claude Code functionality.

### Plan Philosophy: Discovery-First

This plan acknowledges that **OpenCode component loading mechanisms are not fully documented in-repo**. Rather than assume formats, the plan:

1. **Wave 1**: Create minimal config from existing template
2. **Wave 2**: Validate OpenCode behavior empirically (discover loading rules)
3. **Wave 3**: Implement based on validated findings
4. **Wave 4**: Document discoveries

This is a pragmatic approach when authoritative external docs are incomplete.

### Authoritative In-Repo References

| Component | Reference File | Purpose |
|-----------|---------------|---------|
| OpenCode Config | `examples/opencode-dev.json` | Format template |
| Claude Code Config | `.claude-plugin/plugin.json` | Must NOT modify |
| Claude Code Hooks | `hooks/hooks.json` | Source for prompt text |
| Claude Code Agents | `agents/*.md` | Source for body content |
| Claude Code Skills | `skills/` | Source for skill content |
| Test File | `test-specs/Counter.tla` | Canonical test spec |

### Skills Location (Current State)

**Verified from `.claude-plugin/plugin.json` line 15**:
- Claude Code uses `"skills": "./skills/"` → reads from `skills/` directory (6 skills)
- `.claude/skills/` also exists with 3 skills (legacy duplicate, not used by current config)

**For OpenCode**: Discovery needed (Task 4) to determine:
- Does OpenCode read from `skills/` directly?
- Or does OpenCode require `.opencode/skills/`?
- How many skills need copying?

### OpenCode Config Discovery

**How OpenCode finds configuration** (based on common patterns):
- Run `opencode` from repo root
- OpenCode looks for `opencode.json` or `.opencode/opencode.json`

**This will be validated in Task 2.**

---

## Decision Rules (Wave 2 → Wave 3)

Task 2/3/4 produce decision artifacts that MECHANICALLY determine Wave 3 implementation:

### Skills Decision Rule
| Task 4 Observation | Decision | Task 5 Action |
|--------------------|----------|---------------|
| All 6 skills load via `skills/` | `skillsDir = skills/` | Task 5: Verify only, no copy needed |
| Some skills load, some fail | `skillsDir = mixed` | Task 5: Copy failed ones to `.opencode/skills/` |
| No skills load from `skills/` | `skillsDir = .opencode/skills/` | Task 5: Copy all 6 to `.opencode/skills/` |
| Skills require config entry | `skillsDir = needs-config` | Task 5: Add config + copy to `.opencode/skills/` |

**"Loaded" defined as**: `/skill <name>` returns skill content, OR `opencode skills` shows "Registered"
**"Failed" defined as**: "Skill not found" error, OR skill not in registered list

### Agents Decision Rule
| Task 2 Observation | Decision | Task 6 Action |
|--------------------|----------|---------------|
| Agents load from `agents/` with Claude format | `agentsDir = agents/` | Task 6: Verify only |
| Agents require `.opencode/agents/` | `agentsDir = .opencode/agents/` | Task 6: Create 4 agents |
| Agents require different frontmatter | `agentFormat = <fields>` | Task 6: Use discovered format |
| Agents require config entry | `agentsDir = needs-config` | Task 6: Add config + create agents |

**"Loaded" defined as**: Agent appears in `opencode agents --status` OR Agent Log shows "Ready"
**"Failed" defined as**: Agent not listed, OR "Agent not found" error

### Commands Decision Rule
| Task 3 Observation | Decision | Task 8 Action |
|--------------------|----------|---------------|
| All commands work as-is | `commandsWork = YES` | Task 8: Document "no changes needed" |
| Commands fail with "command not found" | `commandsWork = NO (discovery)` | Task 8: Check if config needed |
| Commands fail with frontmatter error | `commandsWork = NO (frontmatter)` | Task 8: Add compatible frontmatter |
| Commands fail with tool error | `commandsWork = PARTIAL` | Task 8: Document limitation |

**Error Pattern Recognition**:
- "Command not found" → Commands may need config entry
- "Invalid YAML" / "Unknown field" → Frontmatter compatibility issue
- "Tool not found" → MCP issue, not command issue

### Hooks Decision Rule
| Task 2 Observation | Decision | Task 7 Action |
|--------------------|----------|---------------|
| `hooks` array config works | `hooksSupported = YES` | Task 7: Full implementation |
| Hooks config rejected/ignored | `hooksSupported = NO` | Task 7: Create prompts.json as documentation only |
| Different hook format needed | `hookFormat = <shape>` | Task 7: Use discovered format |

**"Works" defined as**: Hook fires observable side effect (log message, context injection)
**"Rejected" defined as**: Config validation error, OR hook never fires

---

## Build Dependency

**`dist/index.js` does NOT exist until built.**

- Task 1 creates config that references `./dist/index.js`
- Task 2 runs `npm run build` FIRST before starting OpenCode
- Existence of `dist/index.js` is verified in Task 2, not Task 1

This is intentional: config file is valid JSON referencing a path that will exist after build.

---

## Work Objectives

### Core Objective
Enable TLA+ plugin functionality in OpenCode while maintaining 100% Claude Code compatibility.

### Deliverables (Counts May Change Based on Discovery)

| File/Directory | Purpose | Count Depends On |
|----------------|---------|------------------|
| `.opencode/opencode.json` | Config | Fixed (1 file) |
| `.opencode/skills/` | Skills | Task 4 results |
| `.opencode/agents/` | Agents | Fixed (4 files) |
| `hooks/prompts.json` | Shared prompts | Fixed (1 file) |
| `OPENCODE.md` | Documentation | Fixed (1 file) |

### Definition of Done
- [ ] `cc --plugin-dir $(pwd)` then `/tla-parse @test-specs/Counter.tla` works
- [ ] `opencode` (from repo root) recognizes MCP server
- [ ] Skills accessible in OpenCode (method determined by Task 4)
- [ ] Agents accessible in OpenCode (format determined by Task 2)
- [ ] Commands work in OpenCode (behavior documented)
- [ ] Zero Claude Code regressions

### Guardrails

**Must NOT**:
- Modify `.claude-plugin/plugin.json`
- Modify `hooks/hooks.json`
- Modify `agents/*.md`
- Modify `skills/**/*`
- Delete or rename pre-existing repo files

**Temporary Files**:
- `.sisyphus/opencode-validation-results.md` is a working artifact created during this plan and may be deleted after completion (it is NOT a pre-existing file)

---

## Hooks Integration Strategy

Based on OpenCode's hook consumption model:

**Source**: `hooks/hooks.json` (Claude Code format - prompt-based)
**Target**: `hooks/prompts.json` (OpenCode Prompt Registry format)

**Mapping Strategy**:
| Claude Code Hook | OpenCode Event | prompts.json Key |
|------------------|----------------|------------------|
| SessionStart | `pre_prompt` (session init) | `session_start_hook` |
| PreToolUse | `on_tool_call` with filter | `pre_tool_hook` |
| PostToolUse | `post_response` | `post_tool_hook` |

**OpenCode Config** (`.opencode/opencode.json`):
```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "tlaplus": {
      "type": "local",
      "command": ["node", "./dist/index.js"],
      "enabled": true
    }
  },
  "hooks": [
    {
      "event": "pre_prompt",
      "action": "inject_context",
      "params": {
        "source": "./hooks/prompts.json",
        "key": "session_start_hook"
      }
    }
  ]
}
```

**hooks/prompts.json Format**:
```json
{
  "_source": "hooks/hooks.json",
  "session_start_hook": "[VERBATIM from SessionStart[0].prompt]",
  "pre_tool_hook": "[VERBATIM from PreToolUse[0].hooks[0].prompt]",
  "post_tool_hook": "[VERBATIM from PostToolUse[0].hooks[0].prompt]"
}
```

---

## Hooks Verbatim Copy Rule

**Source of Truth**: `hooks/hooks.json`

**Exact Source Locations** (from hooks/hooks.json structure):
```
hooks/hooks.json JSON structure:
{
  "SessionStart": [{ "type": "prompt", "prompt": "..." }],
  "PreToolUse": [{ ... "hooks": [{ "type": "prompt", "prompt": "..." }] }],
  "PostToolUse": [{ ... "hooks": [{ "type": "prompt", "prompt": "..." }] }]
}
```

**Mapping to `hooks/prompts.json`** (FLAT KEY SCHEMA):
| Source Path | Target Key |
|-------------|------------|
| `SessionStart[0].prompt` | `session_start_hook` |
| `PreToolUse[0].hooks[0].prompt` | `pre_tool_hook` |
| `PostToolUse[0].hooks[0].prompt` | `post_tool_hook` |

**Verbatim Copy Verification Procedure**:
```bash
# Extract prompts from source and verify match
# Step 1: Extract SessionStart prompt from hooks.json
jq -r '.SessionStart[0].prompt' hooks/hooks.json > /tmp/src_session.txt

# Step 2: Extract session_start_hook prompt from prompts.json (FLAT KEY)
jq -r '.session_start_hook' hooks/prompts.json > /tmp/dst_session.txt

# Step 3: Compare (must be identical)
diff /tmp/src_session.txt /tmp/dst_session.txt
# Expected: No output (identical)

# Repeat for pre_tool_hook and post_tool_hook
jq -r '.PreToolUse[0].hooks[0].prompt' hooks/hooks.json > /tmp/src_pre.txt
jq -r '.pre_tool_hook' hooks/prompts.json > /tmp/dst_pre.txt
diff /tmp/src_pre.txt /tmp/dst_pre.txt

jq -r '.PostToolUse[0].hooks[0].prompt' hooks/hooks.json > /tmp/src_post.txt
jq -r '.post_tool_hook' hooks/prompts.json > /tmp/dst_post.txt
diff /tmp/src_post.txt /tmp/dst_post.txt
```

**Note**: If `jq` is not available, use `python -c "import json; ..."` for extraction.

---

## OpenCode Loading Mechanisms (To Be Discovered)

This section documents what we KNOW vs what we need to DISCOVER.

### KNOWN (from in-repo examples)

| Component | Known Format Reference |
|-----------|----------------------|
| MCP Config | `examples/opencode-dev.json` → `{ "mcp": { "name": { "type": "local", "command": [...] }}}` |

### OpenCode Verification Commands (HYPOTHESES - Validate in Task 2)

**IMPORTANT**: The following commands are hypothesized based on user-provided information. Task 2 MUST validate these and record actual behavior.

**Fallback Discovery Hierarchy** (GUARANTEED EXECUTABLE):
When hypothesized commands don't work, follow this exact sequence:

```bash
# Step 1: Discover available CLI subcommands
opencode --help > /tmp/opencode-help.txt
cat /tmp/opencode-help.txt
# Evidence: Record ALL listed subcommands

# Step 2: For each relevant subcommand, discover options
opencode mcp --help > /tmp/mcp-help.txt 2>&1 || echo "mcp subcommand not found"
opencode agent --help > /tmp/agent-help.txt 2>&1 || echo "agent subcommand not found"
opencode skill --help > /tmp/skill-help.txt 2>&1 || echo "skill subcommand not found"
# Evidence: Record actual subcommand names and options

# Step 3: Check for logs/debug output
opencode --version  # Verify OpenCode runs
ls ~/.opencode/logs/ 2>/dev/null || echo "No logs directory found"
# Evidence: Record where logs are stored (if at all)

# Step 4: Start OpenCode and capture startup output
opencode 2>&1 | tee /tmp/opencode-startup.txt &
sleep 5
cat /tmp/opencode-startup.txt
# Evidence: Record any config loading messages or errors
```

**Config Discovery Test** (deterministic proof which config file is read):
```bash
# Step 1: Create test config with obvious marker
echo '{"_test_marker": "opencode-json-root"}' > opencode.json
echo '{"_test_marker": "dot-opencode-folder"}' > .opencode/opencode.json

# Step 2: Start OpenCode, look for config load message in logs/output
# OR intentionally add invalid JSON to one file:
echo 'INVALID JSON' > opencode.json  # Break root config
# Then start OpenCode - if it errors, root config is read
# If it starts fine, .opencode/opencode.json is read

# Step 3: Clean up test files after discovery
rm opencode.json  # Remove test file
# Evidence: Record which config path OpenCode actually uses
```

**1. MCP Tools - How to List** (Hypothesis):
- **Command Palette**: `Ctrl+Shift+P` → `MCP: List Tools`
- **CLI**: `opencode mcp tools --list` (verify this command exists)
- **UI**: Click MCP icon in Secondary Sidebar → shows tree view
- **Fallback**: Check MCP server connection in OpenCode logs
- **Success Criteria**: `tlaplus_mcp_sany_parse`, `tlaplus_mcp_tlc_check` appear in output
- **Evidence to Record**: Exact command used and its output

**2. Agents - How to Verify Loaded** (Hypothesis):
- **CLI**: `opencode agents --status` OR `opencode agent --status` (verify spelling)
- **UI**: Output Channel → select `OpenCode: Agent Log` dropdown
- **Fallback**: Check `opencode agent --help` for actual subcommands
- **Success Criteria**: Agent shows "Ready" heartbeat or appears in list
- **Evidence to Record**: Exact command and output showing agent status

**3. Skills - How to Verify Discovered** (Hypothesis):
- **CLI**: `opencode skills --show-discovered` (verify this command exists)
- **Fallback**: Try `/skill <name>` in chat interface
- **Success Criteria**: Skill shows "Registered" status OR loads when invoked
- **Evidence to Record**: Exact verification method and result

**4. Hooks - Config Format** (Hypothesis):
The hooks configuration format MAY be:
```json
{
  "hooks": [
    {
      "event": "pre_prompt",
      "action": "inject_context",
      "params": {
        "source": "./hooks/prompts.json",
        "key": "session_start_hook"
      }
    }
  ]
}
```
**MUST VALIDATE**:
- Does OpenCode accept `hooks` key in config?
- What `event` names are valid? (`pre_prompt`, `post_response`, `on_tool_call`?)
- What `action` names are valid? (`inject_context`, `log_event`?)
- Does `params.source` + `params.key` work for Prompt Registry?
**Evidence to Record**: Working config that fires hook OR error message showing rejection

**5. Config Schema Validation**:
- Does OpenCode validate config against `$schema`?
- Are `mcp` and `hooks` valid top-level keys?
- **Test**: Start OpenCode with the proposed config; check for schema errors in logs
- **Evidence to Record**: Startup log showing config loaded successfully OR error

---

## Execution Strategy

### Parallel Execution Waves

```
Wave 1 (Setup):
└── Task 1: Create .opencode/opencode.json from template

Wave 2 (Discovery - document all findings):
├── Task 2: Discover OpenCode loading mechanisms
├── Task 3: Test commands in OpenCode  
└── Task 4: Test skills in OpenCode

Wave 3 (Implement based on discoveries):
├── Task 5: Copy skills (count per Task 4)
├── Task 6: Create agents (format per Task 2)
├── Task 7: Create hooks/prompts.json
└── Task 8: Update commands (if needed per Task 3)

Wave 4 (Finalize):
├── Task 9: Documentation with discoveries
└── Task 10: Final verification
```

---

## TODOs

- [ ] 1. Create OpenCode Configuration

  **What to do**:
  - Create `.opencode/` directory
  - Copy `examples/opencode-dev.json` to `.opencode/opencode.json`
  - Update command path to `./dist/index.js`

  **Commands**:
  ```bash
  mkdir -p .opencode
  cp examples/opencode-dev.json .opencode/opencode.json
  # Edit: change "/path/to/..." to "./dist/index.js"
  ```

  **Target Content**:
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

  **Verification**:
  ```bash
  python -m json.tool .opencode/opencode.json  # Valid JSON
  grep '"./dist/index.js"' .opencode/opencode.json  # Path updated
  ```

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: []

  **Acceptance Criteria**:
  - [ ] `.opencode/` directory exists
  - [ ] `.opencode/opencode.json` is valid JSON
  - [ ] Schema URL matches template: `https://opencode.ai/config.json`
  - [ ] Command path is `./dist/index.js`

  **Commit**: YES
  - Message: `chore(opencode): add OpenCode configuration`
  - Files: `.opencode/opencode.json`

---

- [ ] 2. Discover OpenCode Loading Mechanisms

  **What to do**:
  - Start OpenCode and test component loading
  - Document all discoveries in validation results file
  - This is the KEY DISCOVERY task that informs Wave 3

  **Startup**:
  ```bash
  cd /home/zhitingz/tlaplus-ai-tools
  npm run build
  opencode
  ```

  **Discovery Checklist** (record in `.sisyphus/opencode-validation-results.md`):

  ```markdown
  # OpenCode Validation Results

  ## 1. MCP Tools Loading
  
  **Verification Command**: `opencode mcp tools --list`
  **Alternative**: Ctrl+Shift+P → "MCP: List Tools" OR click MCP icon in Secondary Sidebar
  **Expected**: tlaplus_mcp_sany_parse, tlaplus_mcp_tlc_check, etc. appear
  **Result**: WORKING / NOT WORKING
  **Evidence**: [paste tool list output]

  ## 2. Commands Loading
  
  **Test**: Run `/tla-parse @test-specs/Counter.tla`
  **Result**: WORKING / NOT WORKING
  **If working**: Commands load from `commands/` directory
  **If not working**: [document error message]
  **Decision**: commandsWork = YES/NO

  ## 3. Skills Loading
  
  **Verification Command**: `opencode skills --show-discovered`
  **Expected**: Skills show "Registered" status
  **Test**: `/skill tla-spec-review`
  **Result**: ACCESSIBLE / NOT ACCESSIBLE
  **Decision**: skillsDir = skills/ | .opencode/skills/ | needs-config

  ## 4. Agents Loading
  
  **Verification Command**: `opencode agents --status`
  **Alternative**: Check Output Channel → "OpenCode: Agent Log"
  **Expected**: Agent shows "Ready" heartbeat
  **Result**: AGENTS READY / NOT FOUND
  **Decision**: agentsDir = agents/ | .opencode/agents/ | needs-config

  ## 5. Hooks Loading
  
  **Test Config** (add to .opencode/opencode.json):
  ```json
  "hooks": [
    {
      "event": "pre_prompt",
      "action": "inject_context",
      "params": { "source": "./hooks/prompts.json", "key": "session_start_hook" }
    }
  ]
  ```
  **Result**: HOOK FIRES / NO EFFECT / ERROR
  **Decision**: hooksSupported = YES/NO, hookConfigShape = [document]
  ```

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: [`verification-before-completion`]

  **Acceptance Criteria**:
  - [ ] `.sisyphus/opencode-validation-results.md` created
  - [ ] MCP loading documented with evidence
  - [ ] Command loading mechanism documented
  - [ ] Skill loading directories documented
  - [ ] Agent frontmatter requirements documented
  - [ ] Hook config format documented

  **Commit**: NO (temporary working file)

---

- [ ] 3. Test Commands in OpenCode

  **What to do**:
  - Test all 6 commands in OpenCode
  - Document which work and which fail

  **Test Table** (add to validation results):
  | Command | Input | Status | Evidence |
  |---------|-------|--------|----------|
  | `/tla-parse` | `@test-specs/Counter.tla` | ? | [output/error] |
  | `/tla-smoke` | `@test-specs/Counter.tla` | ? | |
  | `/tla-symbols` | `@test-specs/Counter.tla` | ? | |
  | `/tla-check` | `@test-specs/Counter.tla` | ? | |
  | `/tla-review` | `@test-specs/Counter.tla` | ? | Uses Task tool |
  | `/tla-setup` | (none) | ? | |

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: [`verification-before-completion`]

  **Acceptance Criteria**:
  - [ ] All 6 commands tested
  - [ ] Results documented with evidence
  - [ ] Decision recorded: Is Task 8 needed?

  **Commit**: NO (results in validation file)

---

- [ ] 4. Test Skills in OpenCode

  **What to do**:
  - Test all 6 skills in OpenCode
  - Determine which are accessible and which need copying

  **Test Table** (add to validation results):
  | Skill | Location | Status | Evidence |
  |-------|----------|--------|----------|
  | tla-spec-review | skills/ | ? | |
  | tla-debug-violations | skills/ | ? | |
  | tla-create-animations | skills/ | ? | |
  | tla-getting-started | skills/ | ? | |
  | tla-model-checking | skills/ | ? | |
  | tla-refinement-proofs | skills/ | ? | |

  **Decision Output**:
  - If ALL 6 accessible: No skills need copying (Task 5 = verify only)
  - If SOME accessible: Copy only missing ones
  - If NONE accessible: Copy all 6 to `.opencode/skills/`

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: [`verification-before-completion`]

  **Acceptance Criteria**:
  - [ ] All 6 skills tested
  - [ ] Results documented with evidence
  - [ ] Decision recorded: Which skills to copy (list names)

  **Commit**: NO (results in validation file)

---

- [ ] 5. Copy Skills to .opencode/skills/

  **What to do**:
  - Based on Task 4 results, copy skills that need to be accessible in OpenCode
  - Copy entire directories including subdirectories

  **Commands** (adjust list based on Task 4):
  ```bash
  mkdir -p .opencode/skills
  # Copy each skill identified as NOT ACCESSIBLE in Task 4:
  cp -r skills/<skill-name> .opencode/skills/
  ```

  **Verification**:
  ```bash
  # For each copied skill:
  diff -r skills/<name> .opencode/skills/<name>
  # Expected: No output (identical)
  ```

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: []

  **Acceptance Criteria**:
  - [ ] `.opencode/skills/` created (if needed)
  - [ ] All needed skills copied (per Task 4)
  - [ ] `diff -r` confirms exact copies
  - [ ] In OpenCode: previously inaccessible skills now work

  **Commit**: YES (if files created)
  - Message: `feat(opencode): add skills for OpenCode discovery`
  - Files: `.opencode/skills/**/*`

---

- [ ] 6. Create OpenCode-Format Agents

  **What to do**:
  - Based on Task 2 discovered format, create agents
  - Copy body content verbatim from `agents/*.md`

  **Frontmatter** (use format discovered in Task 2):
  ```yaml
  ---
  # Use fields discovered in Task 2
  name: spec-validator
  description: [copy from source]
  # Add other required fields per discovery
  ---
  [BODY COPIED VERBATIM FROM agents/spec-validator.md]
  ```

  **Files**:
  | Source | Destination |
  |--------|-------------|
  | `agents/spec-validator.md` | `.opencode/agents/spec-validator.md` |
  | `agents/config-generator.md` | `.opencode/agents/config-generator.md` |
  | `agents/animation-creator.md` | `.opencode/agents/animation-creator.md` |
  | `agents/trace-analyzer.md` | `.opencode/agents/trace-analyzer.md` |

  **Body Verification Procedure** (exact comparison excluding frontmatter):
  ```bash
  # For each agent, extract body (everything after second ---)
  # Source agent body
  awk '/^---$/{n++; if(n==2){found=1; next}} found' agents/spec-validator.md > /tmp/src_body.txt
  
  # Destination agent body
  awk '/^---$/{n++; if(n==2){found=1; next}} found' .opencode/agents/spec-validator.md > /tmp/dst_body.txt
  
  # Compare (must be identical)
  diff /tmp/src_body.txt /tmp/dst_body.txt
  # Expected: No output (bodies identical)
  
  # Repeat for all 4 agents
  ```

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: []

  **Acceptance Criteria**:
  - [ ] `.opencode/agents/` created
  - [ ] 4 agent files created using Task 2 format
  - [ ] Body content identical to source agents
  - [ ] `git diff agents/` shows nothing (originals unchanged)
  - [ ] In OpenCode: agents appear in list

  **Commit**: YES
  - Message: `feat(opencode): add OpenCode-format agents`
  - Files: `.opencode/agents/*.md`

---

- [ ] 7. Create Shared Hooks Prompts (CONDITIONAL on Task 2 Discovery)

  **This task branches based on Task 2 `hooksSupported` decision:**

  ### Branch A: If `hooksSupported = YES` (hooks work as hypothesized)

  **What to do**:
  - Create `hooks/prompts.json` as OpenCode Prompt Registry
  - Prompts copied VERBATIM from `hooks/hooks.json`
  - Update `.opencode/opencode.json` with hooks array configuration

  **hooks/prompts.json** (Prompt Registry format):
  ```json
  {
    "_source": "hooks/hooks.json",
    "_rule": "All prompts copied VERBATIM",
    "session_start_hook": "[EXACT TEXT from SessionStart[0].prompt]",
    "pre_tool_hook": "[EXACT TEXT from PreToolUse[0].hooks[0].prompt]",
    "post_tool_hook": "[EXACT TEXT from PostToolUse[0].hooks[0].prompt]"
  }
  ```

  **Update .opencode/opencode.json** with hooks array:
  ```json
  {
    "$schema": "https://opencode.ai/config.json",
    "mcp": { ... },
    "hooks": [
      {
        "event": "pre_prompt",
        "action": "inject_context",
        "params": {
          "source": "./hooks/prompts.json",
          "key": "session_start_hook"
        }
      }
    ]
  }
  ```

  **Acceptance (Branch A)**:
  - [ ] `hooks/prompts.json` created with flat key schema
  - [ ] Verbatim verification passes (jq+diff shows no differences)
  - [ ] `.opencode/opencode.json` has `hooks` array
  - [ ] Observable evidence hook fired (log message, context injection detected)

  ### Branch B: If `hooksSupported = NO` (hooks not supported or different format)

  **What to do**:
  - Create `hooks/prompts.json` as DOCUMENTATION ARTIFACT ONLY
  - Do NOT add non-working `hooks` config to `.opencode/opencode.json`
  - Document limitation in OPENCODE.md

  **hooks/prompts.json** (documentation only):
  ```json
  {
    "_comment": "Documentation only - OpenCode hooks not supported in discovered format",
    "_source": "hooks/hooks.json",
    "session_start_hook": "[EXACT TEXT from SessionStart[0].prompt]",
    "pre_tool_hook": "[EXACT TEXT from PreToolUse[0].hooks[0].prompt]",
    "post_tool_hook": "[EXACT TEXT from PostToolUse[0].hooks[0].prompt]"
  }
  ```

  **Acceptance (Branch B)**:
  - [ ] `hooks/prompts.json` created with `_comment` indicating documentation-only
  - [ ] Verbatim verification passes (jq+diff shows no differences)
  - [ ] `.opencode/opencode.json` does NOT have non-working `hooks` config
  - [ ] Limitation documented in validation results

  ### Common to Both Branches

  **Extract Prompts from hooks/hooks.json**:
  ```bash
  cat hooks/hooks.json
  # Extract prompt strings from:
  # - SessionStart[0].prompt
  # - PreToolUse[0].hooks[0].prompt  
  # - PostToolUse[0].hooks[0].prompt
  ```

  **Verbatim Verification** (same for both branches):
  ```bash
  git diff hooks/hooks.json  # Must show nothing
  
  jq -r '.SessionStart[0].prompt' hooks/hooks.json > /tmp/src.txt
  jq -r '.session_start_hook' hooks/prompts.json > /tmp/dst.txt
  diff /tmp/src.txt /tmp/dst.txt  # Must show nothing
  ```

  **Recommended Agent Profile**:
  - **Category**: `unspecified-low`
  - **Skills**: []

  **Commit**: YES
  - Message: `feat(opencode): add shared hooks prompts`
  - Files: `hooks/prompts.json`, `.opencode/opencode.json` (if Branch A)

---

- [ ] 8. Update Commands (Conditional)

  **What to do**:
  - Only if Task 3 showed failures due to frontmatter issues
  - Add OpenCode fields while keeping Claude Code fields

  **Decision**: Check Task 3 results
  - If commands work: Document "no changes needed"
  - If frontmatter errors: Add necessary fields

  **Recommended Agent Profile**:
  - **Category**: `quick`
  - **Skills**: []

  **Acceptance Criteria**:
  - [ ] Decision documented
  - [ ] If changes made: Claude Code regression test passes
  - [ ] `/tla-review` Task tool limitation documented

  **Commit**: CONDITIONAL
  - Message: `feat(opencode): add command compatibility`
  - Files: `commands/*.md` (if changed)

---

- [ ] 9. Create Documentation

  **What to do**:
  - Create `OPENCODE.md` with all discovered information
  - Update `README.md` with OpenCode section

  **OPENCODE.md Structure**:
  ```markdown
  # OpenCode Setup Guide

  ## Quick Start
  ```bash
  npm run build
  opencode
  ```

  ## What Works
  [Fill from Task 2-4 discoveries]

  ## Platform Differences
  [Based on discoveries]

  ## Known Limitations
  [Based on discoveries]
  ```

  **Recommended Agent Profile**:
  - **Category**: `writing`
  - **Skills**: []

  **Acceptance Criteria**:
  - [ ] `OPENCODE.md` created with accurate discoveries
  - [ ] `README.md` updated
  - [ ] All limitations documented

  **Commit**: YES
  - Message: `docs: add OpenCode documentation`
  - Files: `README.md`, `OPENCODE.md`

---

- [ ] 10. Final Verification

  **What to do**:
  - Verify Claude Code (regression)
  - Verify OpenCode (new functionality)
  - Clean up temporary file

  **Claude Code**:
  ```bash
  cc --plugin-dir $(pwd)
  /tla-parse @test-specs/Counter.tla  # Must work
  ```

  **OpenCode**:
  ```bash
  opencode
  # Verify per discoveries in OPENCODE.md
  ```

  **Regression Check**:
  ```bash
  npm test
  git diff hooks/hooks.json   # Nothing
  git diff agents/            # Nothing
  git diff .claude-plugin/    # Nothing
  ```

  **Cleanup** (temporary file created during this plan):
  ```bash
  rm .sisyphus/opencode-validation-results.md
  ```

  **Recommended Agent Profile**:
  - **Category**: `unspecified-low`
  - **Skills**: [`verification-before-completion`]

  **Acceptance Criteria**:
  - [ ] Claude Code works
  - [ ] OpenCode works (per documented capabilities)
  - [ ] Zero regressions
  - [ ] Temporary file deleted

  **Commit**: YES
  - Message: `chore: cleanup validation artifacts`
  - Files: Delete `.sisyphus/opencode-validation-results.md`

---

## `/tla-review` Command Behavior in OpenCode

**Issue**: `/tla-review` uses `Task` tool for agent spawning. OpenCode may not have `Task`.

**Acceptable Degraded Behavior** (within guardrails):
- Command completes with clear message that agent spawning is unavailable
- Parse and smoke test portions still run via MCP tools directly
- User sees partial results rather than complete failure

**Task 3 Acceptance for `/tla-review`**:
| Observation | Status | Task 8 Action |
|-------------|--------|---------------|
| Full functionality (Task tool works) | PASS | No action needed |
| Partial (MCP works, Task fails with clear error) | PARTIAL | Document limitation |
| Complete failure (command crashes) | FAIL | Investigate, document |

**What NOT to do** (per guardrails):
- Do NOT modify `commands/tla-review.md` to remove Task tool usage
- Do NOT create workaround commands
- Only document the limitation

---

## Commit Strategy

| Task | Message | Files |
|------|---------|-------|
| 1 | `chore(opencode): add OpenCode configuration` | `.opencode/opencode.json` |
| 5 | `feat(opencode): add skills for OpenCode discovery` | `.opencode/skills/**/*` |
| 6 | `feat(opencode): add OpenCode-format agents` | `.opencode/agents/*.md` |
| 7 | `feat(opencode): add shared hooks prompts` | `hooks/prompts.json`, `.opencode/opencode.json` |
| 8 | `feat(opencode): add command compatibility` | `commands/*.md` (conditional) |
| 9 | `docs: add OpenCode documentation` | `README.md`, `OPENCODE.md` |
| 10 | `chore: cleanup validation artifacts` | Delete `.sisyphus/opencode-validation-results.md` |

---

## Success Criteria

- [ ] Claude Code: All existing functionality works (zero regressions)
- [ ] OpenCode: MCP tools accessible
- [ ] OpenCode: Skills accessible (method documented)
- [ ] OpenCode: Commands work (or limitations documented)
- [ ] OpenCode: Agents accessible (format documented)
- [ ] Documentation: All discoveries captured in OPENCODE.md
