---
description: Parse and validate TLA+ specification syntax using SANY (OpenCode probe)
agent: build
---

# Parse TLA+ Specification (OpenCode Probe)

This command validates OpenCode's argument substitution behavior and calls the SANY parser.

## Debug Block

[opencode-args]
ARGUMENTS=$ARGUMENTS
1=$1
2=$2
[/opencode-args]

## Implementation

**Step 1: Validate Arguments**

Check that `$1` is provided:
- If `$1` is empty, print "Error: No file path provided. Usage: /tla-parse <path.tla>" and exit
- Print "Raw argument: $1"

**Step 2: Strip Leading @ Symbol**

If `$1` starts with `@`, remove it:
```bash
SPEC_PATH="${1#@}"
```

Otherwise, use `$1` as-is:
```bash
SPEC_PATH="$1"
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

## Test Invocations

After creating this command, test with:

1. `/tla-parse test-specs/Counter.tla` (plain path)
2. `/tla-parse @test-specs/Counter.tla` (@ prefix)
3. Check if `@$1` in template includes file contents

Document results in comments below or in OPENCODE.md.

---

## Test Results

<!-- Document test results here after manual testing -->
