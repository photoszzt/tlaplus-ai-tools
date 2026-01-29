# TLA+ AI Tools - Testing Guide

Comprehensive testing guide for the tlaplus-ai-tools plugin.

## Pre-Testing Checklist

✅ Verification script passes (`npm run verify`)
✅ MCP server compiled (`dist/index.js` exists)
✅ TLA+ tools downloaded (`tools/*.jar` exist)
✅ Java 11+ installed
✅ Node.js 18+ installed

## Testing Levels

### Level 1: Structure Testing (Automated) ✅

**Status**: PASSED

Validates plugin structure, YAML frontmatter, and JSON configs.

```bash
# Already verified:
npm run verify
```

**Checks**:
- ✅ Directory structure
- ✅ Required files present
- ✅ YAML frontmatter valid
- ✅ JSON syntax valid
- ✅ Executable permissions

#### OpenCode Commands Testing

Commands use unified format compatible with both platforms. To test:

```bash
# Ensure commands are synced first
cp commands/tla-*.md .opencode/commands/

# Run E2E (OPENCODE_MODEL env var should be set to your model)
OPENCODE_E2E=1 OPENCODE_MODEL=<your-model> npm run opencode:e2e
```

**CI Lint Tests** (automated):
- Validates all 6 command files exist under `commands/`
- Checks unified frontmatter (Claude Code + OpenCode fields)
- Verifies MCP tool references per command
- Ensures usage examples and `@` handling notes present
- Checks no positional `$N` variables (only `$ARGUMENTS`)
- Run via: `npm test -- opencode-commands-lint`

**Local E2E Testing** (manual):
- Prerequisites: OpenCode installed + model provider configured
- Run via: `OPENCODE_E2E=1 npm run opencode:e2e`
- Validates command execution and output markers
- Skips if `OPENCODE_E2E` not set to `1`

The E2E script runs all 6 commands and checks for deterministic markers:
- `Spec path:` (all commands)
- `CFG used:` (TLC commands)
- `CFG written:` (`/tla-symbols`)
- `Review Summary` (`/tla-review`)

## Level 2: MCP Server Testing

Test the MCP server independently.

#### 2.1 Server Startup Test

```bash
# Test server can start
node dist/index.js --help

# Expected output:
# Usage: tlaplus-ai-tools [options]
# Options:
#   --http              Enable HTTP transport
#   --port <number>     HTTP port (default: 3000)
#   ...
```

#### 2.2 Parse Test

Create a test TLA+ file:

```bash
cat > /tmp/TestSpec.tla << 'EOF'
---- MODULE TestSpec ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\ [][Next]_x
====
EOF
```

Test parsing via MCP (requires MCP client):

```javascript
// Via MCP client
{
  "method": "tools/call",
  "params": {
    "name": "tlaplus_mcp_sany_parse",
    "arguments": {
      "fileName": "/tmp/TestSpec.tla"
    }
  }
}
```

**Expected**: Parse success, no errors

#### 2.3 Symbol Extraction Test

```javascript
// Via MCP client
{
  "method": "tools/call",
  "params": {
    "name": "tlaplus_mcp_sany_symbol",
    "arguments": {
      "fileName": "/tmp/TestSpec.tla"
    }
  }
}
```

**Expected**: JSON response with symbols (Init, Next, Spec, x)

### Level 3: Plugin Integration Testing

Test plugin in Claude Code environment.

#### 3.1 Installation Test

**Method 1: Local Plugin Directory**
```bash
# Start Claude Code with plugin
cc --plugin-dir $(pwd)
```

**Method 2: Global Installation**
```bash
# From plugin directory
npm link
cc
```

**Verify**:
- Plugin shows in `/plugin list`
- Skills show in `/skills list`
- Commands appear in `/help`

#### 3.2 Skills Testing

Test each skill triggers correctly.

**Test tla-getting-started**:
```
User: "I want to learn TLA+"
Expected: Skill loads, provides introduction
```

**Test tla-model-checking**:
```
User: "How do I run model checking?"
Expected: Skill loads, explains TLC workflow
```

**Test tla-spec-review**:
```
User: "Can you review my TLA+ specification?"
Expected: Skill loads, shows review checklist
```

**Test tla-debug-violations**:
```
User: "Help me debug this invariant violation"
Expected: Skill loads, provides debugging workflow
```

**Test tla-create-animations**:
```
User: "Create an animation for my spec"
Expected: Skill loads, explains animation creation
```

**Test tla-refinement-proofs**:
```
User: "How do I prove refinement?"
Expected: Skill loads, explains refinement checking
```

#### 3.3 Commands Testing

Test each command executes correctly.

**Test /tla-parse**:
```bash
# Create test spec
/tla-parse @TestSpec.tla

Expected:
- Reads file
- Calls SANY parse
- Reports "Parsing successful" or shows errors
```

**Test /tla-symbols**:
```bash
/tla-symbols @TestSpec.tla

Expected:
- Extracts symbols
- Displays symbol table
- Offers to generate .cfg file
```

**Test /tla-smoke**:
```bash
/tla-smoke @TestSpec.tla

Expected:
- Runs 3-second smoke test
- Reports results
- Notes if config missing
```

**Test /tla-check**:
```bash
# Create config first
cat > /tmp/TestSpec.cfg << 'EOF'
SPECIFICATION Spec
INVARIANT x \in Nat
EOF

/tla-check @TestSpec.tla

Expected:
- Finds config
- Runs TLC
- Reports model checking results
```

**Test /tla-review**:
```bash
/tla-review @TestSpec.tla

Expected:
- Loads tla-spec-review skill
- Runs checklist
- Spawns spec-validator agent
- Provides review report
```

**Test /tla-setup**:
```bash
/tla-setup

Expected:
- Checks Java
- Checks TLA+ tools
- Checks MCP server
- Reports status
- Offers fixes if issues
```

#### 3.4 Agents Testing

Test agents spawn and execute correctly.

**Test spec-validator**:
```
User: "Validate Counter.tla"

Expected:
- Agent spawns
- Reads spec
- Runs SANY parse
- Runs smoke test
- Generates validation report
```

**Test config-generator**:
```
User: "Generate config for Counter.tla"

Expected:
- Agent spawns
- Extracts symbols
- Creates .cfg file
- Explains customization
```

**Test animation-creator**:
```
User: "Create animation for Counter.tla"

Expected:
- Agent spawns
- Analyzes spec
- Generates CounterAnim.tla
- Explains usage
```

**Test trace-analyzer**:
```
User: "Analyze this counterexample: [paste trace]"

Expected:
- Agent spawns
- Parses trace
- Explains violation
- Suggests fixes
```

#### 3.5 Hooks Testing

Test hooks activate on appropriate events.

**Test SessionStart hook**:
```
1. Start Claude Code with plugin
2. First message after startup

Expected:
- Silent if tools present
- Warning if tools missing
- Suggestion to run /tla-setup if issues
```

**Test PreToolUse hook (Write/Edit .tla)**:
```
1. Create or edit a .tla file
2. Use Write or Edit tool

Expected:
- Parse runs automatically
- Warning shown if parse fails
- Write/edit proceeds regardless
```

**Test PostToolUse hook (Write .tla)**:
```
1. Create NEW .tla file
2. No corresponding .cfg exists

Expected:
- Suggestion: "Run /tla-symbols to generate config?"
- Only for new files, not edits
```

### Level 4: End-to-End Workflows

Test complete user workflows.

#### Workflow 1: New User Learning TLA+

```
1. User: "I want to learn TLA+"
   → tla-getting-started skill loads

2. Follow skill guidance to create Counter.tla
   → PostToolUse hook suggests config generation

3. User: "/tla-symbols @Counter.tla"
   → Command generates Counter.cfg

4. User: "/tla-smoke @Counter.tla"
   → Quick validation passes

5. User: "/tla-check @Counter.tla"
   → Full model checking passes
```

#### Workflow 2: Debugging a Violation

```
1. User runs model checking, gets violation

2. User: "/tla-review @Spec.tla"
   → Review identifies potential issues

3. User: "Analyze this counterexample: [trace]"
   → trace-analyzer agent explains violation

4. User fixes spec based on suggestions

5. User: "/tla-smoke @Spec.tla"
   → Verify fix works

6. User: "/tla-check @Spec.tla"
   → Full verification passes
```

#### Workflow 3: Creating an Animation

```
1. User: "Create animation for my queue spec"
   → animation-creator agent spawns

2. Agent generates QueueAnim.tla

3. User: "/tla-check @QueueAnim.tla"
   → Generates animation

4. User views animated states
```

### Level 5: Error Handling Testing

Test error conditions and recovery.

#### Missing Dependencies
```
Test: Start without Java
Expected: Clear error message, instructions to install

Test: Missing TLA+ tools
Expected: /tla-setup offers to download

Test: Missing config file
Expected: Helpful message, suggest /tla-symbols
```

#### Invalid Input
```
Test: /tla-parse @NonExistent.tla
Expected: File not found error

Test: /tla-check with syntax errors
Expected: Parse errors shown first

Test: Invalid .cfg file
Expected: Config syntax error reported
```

#### Tool Failures
```
Test: Java crashes
Expected: Error captured, user notified

Test: TLC times out
Expected: Timeout detected, state reported

Test: Out of memory
Expected: Memory error, suggestions provided
```

## Test Results Template

```markdown
### Test: [Component Name]

**Date**: YYYY-MM-DD
**Tester**: Name
**Status**: ✅ PASS / ⚠️ PARTIAL / ❌ FAIL

**Steps**:
1. Step 1
2. Step 2
3. Step 3

**Expected Result**:
[What should happen]

**Actual Result**:
[What actually happened]

**Notes**:
[Any observations]

**Issues Found**:
[List any bugs or problems]
```

## Known Limitations

### Current Limitations

1. **MCP Server Testing**: Requires actual Claude Code/OpenCode environment
2. **Agent Testing**: Needs full Claude Code to spawn agents
3. **Hook Testing**: Requires interactive session to trigger
4. **Skill Triggering**: Depends on Claude's matching logic

### What Can Be Tested Standalone

✅ YAML/JSON syntax validation
✅ File structure verification
✅ Script execution
✅ MCP server startup
✅ Direct MCP tool calls (with client)

### What Requires Claude Code

⏳ Skill triggering
⏳ Command execution
⏳ Agent spawning
⏳ Hook activation
⏳ Full workflow testing

## Continuous Testing

### During Development

```bash
# After any change
npm run verify               # Structure check
npm run build               # Rebuild if code changed
npm test                    # Unit tests (if added)
```

### Before Release

- [ ] All Level 1 tests pass
- [ ] MCP server tests pass
- [ ] Skills trigger correctly
- [ ] Commands execute properly
- [ ] Agents spawn and work
- [ ] Hooks activate appropriately
- [ ] Workflows complete successfully
- [ ] Error handling works
- [ ] Documentation accurate

## Test Coverage Summary

**Automated Tests**: ✅ 100%
- Structure validation
- Syntax validation
- Basic verification

**Manual Tests**: ⏳ Pending user testing
- Plugin integration
- Skills triggering
- Commands execution
- Agents spawning
- Hooks activation
- End-to-end workflows

## Next Steps

1. ✅ Structure testing complete
2. → User testing in Claude Code
3. → Collect feedback
4. → Fix any issues found
5. → Iterate and improve

## Bug Reporting

If you find issues during testing:

1. Note the exact steps to reproduce
2. Capture error messages
3. Check relevant log files
4. Create issue with details
5. Tag with severity (critical/major/minor)

## Testing Checklist

Before marking testing complete:

- [ ] Verification script passes
- [ ] All skills load correctly
- [ ] All commands execute
- [ ] All agents spawn
- [ ] All hooks activate
- [ ] Workflows complete
- [ ] Errors handled gracefully
- [ ] Documentation matches behavior
- [ ] Cross-platform tested (if possible)
- [ ] Performance acceptable

---

**Testing Status**: Structure tests PASSED ✅
**Next**: User testing in Claude Code environment
