# OpenCode Commands - Learnings

## Task 1: Created OpenCode Command Probe (2026-01-28)

**File Created:** `.opencode/commands/tla-parse.md`

**Purpose:** Validate OpenCode's command discovery and argument substitution behavior.

**Key Features:**
- Frontmatter with `description` and `agent: build`
- Debug block with exact format: `[opencode-args]` ... `[/opencode-args]`
- Prints `$ARGUMENTS`, `$1`, `$2` for inspection
- Strips leading `@` from `$1` using bash parameter expansion: `${1#@}`
- Validates `.tla` extension and file existence
- Calls `tlaplus_mcp_sany_parse` with resolved path
- Includes test invocation instructions

**Expected Behavior:**
1. Command auto-discovered from `.opencode/commands/*.md`
2. Command name derived from filename: `tla-parse.md` → `/tla-parse`
3. `$ARGUMENTS` contains full argument string
4. `$1` contains first argument (may include `@` prefix)
5. `$2` contains second argument (if provided)

**Next Steps:**
- Manual testing required with 3 invocations:
  1. `/tla-parse test-specs/Counter.tla` (plain path)
  2. `/tla-parse @test-specs/Counter.tla` (@ prefix)
  3. Check if template-time `@$1` includes file contents
- Document results in command file or OPENCODE.md

**Implementation Notes:**
- Used bash parameter expansion `${1#@}` for @ stripping (POSIX-compatible)
- Validation checks before MCP tool call prevent cryptic errors
- Debug block format matches plan specification exactly
- Test spec exists: `test-specs/Counter.tla` (16 lines, valid TLA+)


## Task 3: Jest Lint Tests for OpenCode Commands

### Implementation Summary
Created `src/__tests__/opencode-commands-lint.test.ts` with comprehensive validation:

**Test Coverage:**
1. **File Existence**: Validates all 6 expected command files exist
2. **Frontmatter Validation**: Parses YAML frontmatter and checks required keys
3. **MCP Tool References**: Verifies each command references appropriate MCP tools
4. **Usage Examples**: Checks for plain path examples and @ handling notes
5. **Documentation Accuracy**: Ensures OPENCODE.md doesn't claim commands unsupported
6. **Content Quality**: Validates implementation sections and step-by-step instructions

**Key Design Decisions:**
- Minimal frontmatter parser (no dependencies) - simple key:value regex parsing
- Placed under `src/__tests__/` to match Jest roots configuration
- Actionable failure messages with specific tool/file names
- CI-safe (no command execution, only static file validation)

**MCP Tool Mapping (per plan):**
- tla-parse → tlaplus_mcp_sany_parse
- tla-symbols → tlaplus_mcp_sany_parse, tlaplus_mcp_sany_symbol
- tla-smoke → tlaplus_mcp_tlc_smoke
- tla-check → tlaplus_mcp_tlc_check
- tla-review → parse + symbols + smoke
- tla-setup → no MCP tools (validation only)

**Test Results:**
- Tests correctly fail for missing 5 command files (only tla-parse.md exists)
- Tests correctly fail for OPENCODE.md claiming commands unsupported
- Tests pass for existing tla-parse.md (validates structure)
- TypeScript compilation passes with no errors

**Next Steps:**
- Task 2 will create remaining 5 command files
- Task 4 will update OPENCODE.md to reflect command support
- Once complete, all tests will pass in CI

## Task 5: Hardened Jest Lint Tests

### Edge Cases Added
1. **Exact count validation**: Test now ensures exactly 6 command files exist (not just "some")
   - Provides actionable error messages listing missing/unexpected files
   
2. **Filename/command name matching**: Validates that filenames match command names referenced in content
   - Checks for `/command-name` pattern in file content
   - Example: `tla-parse.md` must contain `/tla-parse`

3. **OPENCODE.md documentation accuracy**: Enhanced check for outdated "not supported" claims
   - Uses multiple regex patterns to catch various formats
   - Provides actionable error message with specific patterns found
   - Suggests corrective action

4. **Special handling for tla-setup.md**: 
   - Skips file argument and @ handling tests (setup command takes no file args)
   - Conditional test logic based on command type

### Test Improvements
- Replaced `fail()` with `throw new Error()` (Jest best practice)
- Added detailed error messages for all validation failures
- Tests now fail with actionable guidance when issues detected

### Verification
- 71 tests passing
- 1 test correctly failing (OPENCODE.md outdated claims) - will pass after Task 4 completes
- All edge cases from plan (lines 745-748) implemented
