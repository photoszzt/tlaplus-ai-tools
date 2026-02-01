---
name: tla-parse
description: Parse and validate TLA+ specification syntax using SANY
argument-hint: "@spec.tla"
allowed-tools:
  [Read, Bash, Grep, mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse]
agent: build
---

# Parse TLA+ Specification

## Implementation

**Step 1: Validate Arguments**

Check that `$ARGUMENTS` is provided:

- If `$ARGUMENTS` is empty, print "Error: No file path provided. Usage: /tla-parse <path.tla>" and exit
- Print "Raw argument: $ARGUMENTS"

**Step 2: Strip Leading @ Symbol**

If `$ARGUMENTS` starts with `@`, remove it:

```bash
SPEC_PATH="${ARGUMENTS#@}"
```

Otherwise, use `$ARGUMENTS` as-is:

```bash
SPEC_PATH="$ARGUMENTS"
```

Print "Spec path: $SPEC_PATH"

**Step 3: Validate File Path**

Check that the file exists and ends with `.tla`:

- If path doesn't end with `.tla`, print "Error: File must have .tla extension" and exit
- If file doesn't exist, print "Error: File not found: $SPEC_PATH" and exit
- Print "File validated: $SPEC_PATH"

**Step 4: Call MCP Tool**

Invoke the SANY parser:

```
tlaplus_mcp_sany_parse --fileName "$SPEC_PATH"
```

**Step 5: Report Results**

If parsing succeeds:

- Print "✓ Parsing successful. No errors found."

If parsing fails:

- Print "✗ Parsing failed. See errors above."
- Offer to explain common TLA+ syntax errors if user wants help
