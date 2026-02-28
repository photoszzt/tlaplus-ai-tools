---
name: tla-parse
description: Parse and validate TLA+ specification syntax and semantics using SANY
version: 1.0.0
allowed-tools: [Read, Grep, mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse]
---

# Parse TLA+ Specification

Validate the syntax and semantics of a TLA+ specification using the SANY parser. This catches errors before model checking.

**IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash.**

## Usage

**Plain path:**
```
/tla-parse test-specs/Counter.tla
/tla-parse specs/MySpec.tla
```

**With @ prefix:**
```
/tla-parse @test-specs/Counter.tla
/tla-parse @Counter.tla
```

Both forms work identically---the `@` is optional and strips during path normalization.

## What This Does

SANY (Semantic ANalYzer) performs comprehensive syntax and semantic validation:

- **Syntax Checking** - Catches parse errors, malformed operators, incorrect indentation
- **Semantic Analysis** - Validates operator definitions, type compatibility, module imports
- **Module Resolution** - Verifies EXTENDS and INSTANCE statements reference valid modules
- **Error Reporting** - Provides line/column locations and helpful error messages

## When to Use

Use `/tla-parse` to:

- **Validate new specifications** before generating configs or running model checking
- **Catch typos and syntax errors** early
- **Understand semantic issues** with operator definitions or module dependencies
- **Get detailed error messages** with exact line locations

Do NOT use for model checking---that's `/tla-check` or `/tla-smoke`.

## Common Error Messages

| Error | Cause | Fix |
|-------|-------|-----|
| `Unexpected token` | Syntax error (typo, bracket mismatch) | Review line and check parentheses, EXTENDS clause |
| `Unknown operator` | Reference to undefined operator or typo | Check operator name spelling; ensure it's defined |
| `Module not found` | EXTENDS or INSTANCE references non-existent module | Verify module name and path; check for typos |
| `Level conflict` | Mixing constants and variables incorrectly | Ensure operators have consistent levels (constant/variable) |
| `Type mismatch` | Incompatible types in operator (e.g., set vs element) | Review operator definitions and usage |

## Examples

### Successful Parse

```
/tla-parse @test-specs/Counter.tla

✓ Parsing successful. No errors found.
```

### Syntax Error (Typo)

```
/tla-parse @specs/Bad.tla

✗ Parsing failed. See errors above.
- Line 5: Unexpected token 'VARIBLES' (did you mean 'VARIABLE'?)
```

### Missing Import

```
/tla-parse @specs/MySpec.tla

✗ Parsing failed. See errors above.
- Line 2: Module 'Sequences' not found in EXTENDS
- Hint: Consider adding Sequences to CommunityModules or use Naturals/Integers instead
```

## Next Steps

- **Parse succeeds** -> Run `/tla-symbols` to generate `.cfg`, then `/tla-smoke` for quick test
- **Parse fails** -> Fix errors and re-run `/tla-parse` until valid
- **Need help** -> Review [tla-getting-started skill](skill://tla-getting-started) or knowledge base articles

## Related Skills

- `/tla-symbols` - Extract symbols and generate TLC config
- `/tla-smoke` - Quick 3-second smoke test
- `/tla-check` - Full exhaustive model checking
- `/tla-review` - Comprehensive spec review

## Knowledge Base

See these articles for TLA+ syntax help:

- [tla-indentation.md](resource://knowledgebase/tla-indentation.md) - Proper TLA+ indentation conventions
- [tla-functions-operators.md](resource://knowledgebase/tla-functions-operators.md) - Defining operators and functions
- [tla-functions-records-sequences.md](resource://knowledgebase/tla-functions-records-sequences.md) - Data structure syntax
- [tla-extends-instance.md](resource://knowledgebase/tla-extends-instance.md) - Module dependencies

---

## Implementation

**Step 1: Validate Arguments**

Check that the spec file path was provided as the argument to this skill:

- If no argument is provided, print "Error: No file path provided. Usage: /tla-parse <path.tla>" and exit
- Print "Raw argument: <argument>"

**Step 2: Strip Leading @ Symbol**

If the argument starts with `@`, remove it to get the spec path. Otherwise, use the argument as-is.

Print "Spec path: <spec_path>"

**Step 3: Validate File Path**

Check that the file exists and ends with `.tla`:

- If path doesn't end with `.tla`, print "Error: File must have .tla extension" and exit
- Use the Read tool to verify the file exists. If file doesn't exist, print "Error: File not found: <spec_path>" and exit
- Print "File validated: <spec_path>"

**Step 4: Call MCP Tool**

Invoke the SANY parser:

```
mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse --fileName "<spec_path>"
```

**Step 5: Report Results**

If parsing succeeds:

- Print "Parsing successful. No errors found."

If parsing fails:

- Print "Parsing failed. See errors above."
- Offer to explain common TLA+ syntax errors if user wants help
