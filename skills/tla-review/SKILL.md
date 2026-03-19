---
name: tla-review
description: >-
  This skill runs a comprehensive review of a TLA+ specification including parsing, symbol extraction, smoke testing, and best practices checklist.
  It should be used when the user asks to "review my spec", "audit my spec",
  "is my spec good", "spec quality check", "comprehensive review",
  "best practices check", "check spec quality", "spec review", "analyze my spec", "what's wrong with my spec",
  "review my TLA+ spec", "spec health check", "validate my specification",
  or wants a full quality assessment.
version: 1.0.0
allowed-tools:
  - Read
  - Grep
  - Write
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke
---

# TLA+ Specification Review

Run a comprehensive review of your TLA+ specification including parsing, symbol extraction, smoke testing, and best practices checklist.

**IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
/tla-review test-specs/Counter.tla
/tla-review test-specs/Counter.tla test-specs/Counter.cfg
/tla-review test-specs/Counter.tla --no-smoke
```

All forms work identically. See `skills/shared/path-normalization.md` for path normalization rules.

## What This Does

1. Validates and normalizes the spec path from the argument
2. Runs SANY parser to check syntax and semantics
3. Extracts symbols to analyze spec structure
4. Runs smoke test (unless `--no-smoke` flag present)
5. Generates comprehensive review report with recommendations

## Implementation

**Step 1: Normalize Spec Path**

Take the spec file path provided as the argument to this skill. If it starts with `@`, strip the leading `@`.

Print `Spec path: <spec_path>`

**Step 2: Validate File**

- Check path ends with `.tla`
- Use the Read tool to verify the file exists on disk
- If validation fails, print error and exit

**Step 3: Parse Flags**

Extract flags from the argument:

- `--no-smoke`: Skip smoke test (default: smoke enabled)

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Step 5: Run SANY Parser**

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` with `fileName=<spec_path>`

Store result:

- `PARSE_SUCCESS=true/false`
- `PARSE_ERRORS=<error list>`

**Step 6: Extract Symbols**

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol` with:

- `fileName=<spec_path>`
- `includeExtendedModules=false`

Store result:

- `SYMBOLS=<symbol extraction result>`
- Extract: `CONSTANTS`, `VARIABLES`, `INIT`, `NEXT`, `SPEC`, `INVARIANTS`, `PROPERTIES`

**Step 7: Run Smoke Test (if enabled)**

If smoke is enabled (no `--no-smoke` flag):

Apply the CFG Selection Algorithm documented in `skills/shared/cfg-selection-algorithm.md`.

If Phase 1 finds no config file, set `SMOKE_SKIPPED=true` and continue to review instead of exiting.

Store final cfg path in `FINAL_CFG`.

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke` with:

- `fileName=<SPEC_PATH>`
- `cfgFile=<FINAL_CFG>`
- `seconds=3`

Store result:

- `SMOKE_SUCCESS=true/false`
- `SMOKE_VIOLATIONS=<violation list>`

**Step 8: Generate Review Report**

Print comprehensive review summary:

```
═══════════════════════════════════════════════════════════
TLA+ SPECIFICATION REVIEW
═══════════════════════════════════════════════════════════

Spec: <SPEC_PATH>

─────────────────────────────────────────────────────────
1. SYNTAX & SEMANTICS (SANY Parser)
─────────────────────────────────────────────────────────

<if PARSE_SUCCESS>
Parsing successful. No syntax errors.
<else>
Parsing failed. Errors found:
<PARSE_ERRORS>
<endif>

─────────────────────────────────────────────────────────
2. STRUCTURE ANALYSIS (Symbol Extraction)
─────────────────────────────────────────────────────────

Constants: <CONSTANTS or "None">
Variables: <VARIABLES or "None">
Init: <INIT or "Not detected">
Next: <NEXT or "Not detected">
Spec: <SPEC or "Not detected">
Invariants: <INVARIANTS or "None">
Properties: <PROPERTIES or "None">

<if no INIT or no NEXT or no SPEC>
Warning: Missing behavior specification
  - Ensure Init, Next, and Spec are defined
  - Or define INIT/NEXT in .cfg file
<endif>

<if CONSTANTS non-empty>
Warning: Constants require assignment
  - Edit .cfg file to assign concrete values
  - Example: CONSTANT MaxValue = 10
<endif>

─────────────────────────────────────────────────────────
3. SMOKE TEST (3-second simulation)
─────────────────────────────────────────────────────────

<if SMOKE_SKIPPED>
Skipped (no config file or --no-smoke flag)
<else if SMOKE_SUCCESS>
Smoke test passed
  CFG used: <FINAL_CFG>
  No violations found in random simulation
<else>
Smoke test failed
  CFG used: <FINAL_CFG>
  Violations detected:
<SMOKE_VIOLATIONS>
<endif>

─────────────────────────────────────────────────────────
4. BEST PRACTICES CHECKLIST
─────────────────────────────────────────────────────────

<Check and report on:>

Module documentation
  - Does module have header comment explaining purpose?
  - Are complex operators documented?

Type invariants
  - Are type invariants defined for all variables?
  - Example: TypeInvariant == var \in ExpectedType

Safety properties
  - Are safety invariants defined?
  - Do they cover critical correctness conditions?

Liveness properties
  - Are liveness properties defined if needed?
  - Example: <>[]Termination

Constant bounds
  - Are constants bounded to reasonable values?
  - Large constants cause state explosion

Symmetry
  - Can symmetry sets reduce state space?
  - Example: SYMMETRY SymmetrySet

State constraints
  - Are state constraints needed to limit exploration?
  - Example: CONSTRAINT StateConstraint

─────────────────────────────────────────────────────────
5. RECOMMENDATIONS
─────────────────────────────────────────────────────────

<Generate specific recommendations based on findings:>

<if PARSE_ERRORS>
-> Fix syntax errors before proceeding
<endif>

<if no config file>
-> Run: /tla-symbols <SPEC_PATH>
<endif>

<if CONSTANTS non-empty and no config>
-> Assign constant values in .cfg file
<endif>

<if SMOKE_VIOLATIONS>
-> Fix violations found in smoke test
-> Run: /tla-check for full counterexample
<endif>

<if SMOKE_SUCCESS or SMOKE_SKIPPED>
-> Run: /tla-check for exhaustive verification
<endif>

<if no INVARIANTS>
-> Consider adding type and safety invariants
<endif>

<if no PROPERTIES>
-> Consider adding liveness properties if applicable
<endif>

═══════════════════════════════════════════════════════════
REVIEW COMPLETE
═══════════════════════════════════════════════════════════
```

## Example Output

The review report follows the template in Step 8 above exactly. Each section is populated with actual results from SANY parsing, symbol extraction, smoke testing, and best practices analysis. The template is self-explanatory and requires no additional example.
