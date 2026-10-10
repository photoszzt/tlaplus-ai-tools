---
name: tla-parse
description: >-
  This skill parses and validates TLA+ specification syntax and semantics using SANY.
  It should be used when the user asks to "check syntax", "validate my spec",
  "is my spec valid", "parse errors", "syntax errors", "SANY errors",
  "SANY", "parse my TLA+ file", "check my TLA+ syntax", "does my spec compile",
  "find errors in my spec", "is my TLA+ correct", "lint my spec", "check for errors",
  "why won't my spec parse", or "check my spec for errors".
version: 1.0.0
allowed-tools:
  - Read
  - Grep
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse
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

Both forms work identically. See `skills/shared/path-normalization.md` for path normalization rules.

## What This Does

SANY (Semantic ANalYzer) performs comprehensive syntax and semantic validation:

- **Syntax Checking** - Catches parse errors, malformed operators, incorrect indentation
- **Semantic Analysis** - Validates operator definitions, type compatibility, module imports
- **Module Resolution** - Verifies EXTENDS and INSTANCE statements reference valid modules
- **Error Reporting** - Provides line/column locations and helpful error messages

## When to Use

Use `/tla-parse` for syntax-only validation without model checking. Note that `/tla-check` also catches parse errors as part of its workflow, so `/tla-parse` is most useful when you want to validate syntax without running the model checker. For model checking, use `/tla-check` or `/tla-smoke`.

## Common Error Messages

| Error              | Cause                                                 | Fix                                                         |
| ------------------ | ----------------------------------------------------- | ----------------------------------------------------------- |
| `Unexpected token` | Syntax error (typo, bracket mismatch)                 | Review line and check parentheses, EXTENDS clause           |
| `Unknown operator` | Reference to undefined operator or typo               | Check operator name spelling; ensure it's defined           |
| `Module not found` | EXTENDS or INSTANCE references non-existent module    | Verify module name and path; check for typos                |
| `Level conflict`   | Mixing constants and variables incorrectly            | Ensure operators have consistent levels (constant/variable) |
| `Type mismatch`    | Incompatible types in operator (e.g., set vs element) | Review operator definitions and usage                       |

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
- **Need help** -> See `/tla-getting-started` or knowledge base articles

## Related Skills

- `/tla-symbols` - Extract symbols and generate TLC config
- `/tla-smoke` - Quick 3-second smoke test
- `/tla-check` - Full exhaustive model checking
- `/tla-review` - Comprehensive spec review

## Knowledge Base

See these knowledge base articles for TLA+ syntax help:

- `resources/knowledgebase/tla-indentation.md` - Proper TLA+ indentation conventions
- `resources/knowledgebase/tla-functions-operators.md` - Defining operators and functions
- `resources/knowledgebase/tla-functions-records-sequences.md` - Data structure syntax
- `resources/knowledgebase/tla-extends-instance.md` - Module dependencies

These articles are also accessible programmatically via the `knowledge` MCP resource.

---

## Implementation

**Step 1: Validate Arguments**

Check that the spec file path was provided as the argument to this skill:

- If no argument is provided, print "Error: No file path provided. Usage: /tla-parse <path.tla>" and exit
- Print "Raw argument: <argument>"

**Step 2: Normalize Path**

Apply path normalization per `skills/shared/path-normalization.md`: if the argument starts with `@`, remove it to get the spec path. Otherwise, use the argument as-is.

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

If `isError` is true, report the failure and its diagnostics. Java/toolchain failures
are failed parses even when no syntax error location is available. Report success
only when the tool explicitly confirms a successful parse.

If parsing succeeds:

- Print "Parsing successful. No errors found."

If parsing fails:

- Print "Parsing failed. See errors above."
- Offer to explain common TLA+ syntax errors if user wants help
