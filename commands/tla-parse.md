---
name: tla-parse
description: Parse and validate TLA+ specification syntax using SANY
argument-hint: "@spec.tla"
allowed-tools: [Read, Bash, Grep]
---

# Parse TLA+ Specification

Parse and validate TLA+ specification files using the SANY parser to detect syntax and semantic errors.

## Usage

```
/tla-parse @Counter.tla
/tla-parse path/to/Spec.tla
```

## What This Command Does

1. Reads the specified TLA+ file
2. Invokes SANY parser via MCP tool `tlaplus_mcp_sany_parse`
3. Reports syntax and semantic errors with line numbers
4. Offers to explain common errors if issues found

## When to Use

- Before running model checker (quick syntax validation)
- After editing a spec (verify changes are valid)
- When learning TLA+ (understand syntax errors)
- As part of commit workflow (validate before committing)

## Output

**Success**: "Parsing successful. No errors found."

**Errors**: Shows error messages with:
- Line and column numbers
- Error descriptions
- Suggestions for common mistakes

## Common Errors Explained

### Missing Module Delimiters

**Error**: "Expecting module begin or end"

**Fix**: Ensure module starts with `---- MODULE Name ----` and ends with `====`

### Undefined Symbols

**Error**: "Unknown operator: SymbolName"

**Fix**: Check for:
- Typos in variable/constant names
- Missing EXTENDS clause for standard modules
- Undefined operators

### Primed Variable Errors

**Error**: "Primed variable in non-action context"

**Fix**: Remove primes (`'`) from Init predicate and invariants. Primes only belong in Next actions.

### EXCEPT Syntax

**Error**: "Syntax error in EXCEPT"

**Fix**: Use `[f EXCEPT ![x] = y]` not `[f EXCEPT [x] = y]` (note the `!`)

## Tips

- Parse before model checking to catch syntax errors early
- Use with `@file` syntax for quick file selection
- Parsing is fast (< 1 second for most specs)
- SANY catches many errors TLC would find later

## Related Commands

- `/tla-smoke` - Quick model check after parsing
- `/tla-symbols` - Extract symbols after successful parse
- `/tla-review` - Comprehensive spec review
- `/tla-setup` - Verify TLA+ tools installation

## Related Skills

- `tla-getting-started` - Learn TLA+ syntax basics
- `tla-spec-review` - Full specification review checklist

## Implementation

Read the TLA+ file and call the MCP tool:

```
tlaplus_mcp_sany_parse --fileName /absolute/path/to/file.tla
```

Handle errors by parsing SANY output and presenting user-friendly messages. Offer contextual help for common error patterns.
