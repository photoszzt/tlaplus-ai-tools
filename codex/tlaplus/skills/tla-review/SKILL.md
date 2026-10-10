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
---

# TLA+ Specification Review

Run a comprehensive review of your TLA+ specification including parsing, symbol extraction, smoke testing, and best practices checklist.

**IMPORTANT: Always use the TLA+ MCP tools named in this skill. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
$tla-review test-specs/Counter.tla
$tla-review test-specs/Counter.tla test-specs/Counter.cfg
$tla-review test-specs/Counter.tla --no-smoke
```

All forms work identically. See `codex/tlaplus/shared/path-normalization.md` for path normalization rules.

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
- Read the file to verify the file exists on disk
- If validation fails, print error and exit

**Step 3: Parse Flags**

Extract flags from the argument:

- `--no-smoke`: Skip smoke test (default: smoke enabled)

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Step 5: Run SANY Parser**

Call `mcp__tlaplus__tlaplus_mcp_sany_parse` with `fileName=<spec_path>`

Store result:

- `PARSE_SUCCESS=true` only for an explicit successful parse with `isError` not true; otherwise false
- `PARSE_ERRORS=<error list>`

**Step 6: Extract Symbols**

Call `mcp__tlaplus__tlaplus_mcp_sany_symbol` with:

- `fileName=<spec_path>`
- `includeExtendedModules=false`

Store result:

- `SYMBOLS=<symbol extraction result>`
- Extract: `CONSTANTS`, `VARIABLES`, `INIT`, `NEXT`, `SPEC`, `INVARIANTS`, `PROPERTIES`

**Step 7: Run Smoke Test (if enabled)**

If smoke is enabled (no `--no-smoke` flag):

Apply the CFG Selection Algorithm documented in `codex/tlaplus/shared/cfg-selection-algorithm.md`.

If Phase 1 finds no config file, set `SMOKE_SKIPPED=true` and continue to review instead of exiting. This intentionally overrides the CFG algorithm's default exit behavior so the review can still provide value without a config file.

Store final cfg path in `FINAL_CFG`.

Call `mcp__tlaplus__tlaplus_mcp_tlc_smoke` with:

- `fileName=<SPEC_PATH>`
- `cfgFile=<FINAL_CFG>`

Use the tool's default three-second simulation; do not pass a `seconds` argument.

Store result:

- `SMOKE_SUCCESS=true` only for completed simulation with exit code zero and no violations
- `SMOKE_ERROR=<parser/config/process failure, timeout, or cancellation, if any>`
- `SMOKE_VIOLATIONS=<violation list>`

**Step 8: Generate Review Report**

Read `resources/knowledgebase/tla-review-guidelines.md` from this plugin's root
and evaluate its applicable guidelines alongside the checklist below. This is
the imported upstream guidance; read the current file rather than relying on
a copied checklist alone.

If model state strings or dynamically constructed record keys contain non-ASCII
text, flag TLC's fingerprinting and serialization limitations. Read
`codex/tlaplus/skills/tla-getting-started/references/syntax-basics.md` from the plugin root for
the upstream evidence. A run reporting fingerprint collisions must not be
presented as successful verification.

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
<else if SMOKE_ERROR>
Smoke test incomplete
  CFG used: <FINAL_CFG>
  Cause: <SMOKE_ERROR>
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

<Evaluate each item and mark as [pass], [warn], or [fail]:>

[pass/warn/fail] Module documentation
  - Does module have header comment explaining purpose?
  - Are complex operators documented?

[pass/warn/fail] Type invariants
  - Are type invariants defined for all variables?
  - Example: TypeInvariant == var \in ExpectedType

[pass/warn/fail] Safety properties
  - Are safety invariants defined?
  - Do they cover critical correctness conditions?

[pass/warn/fail] Liveness properties
  - Are liveness properties defined if needed?
  - Example: <>[]Termination

[pass/warn/fail] Constant bounds
  - Are constants bounded to reasonable values?
  - Large constants cause state explosion

[pass/warn/fail] Symmetry
  - Can symmetry sets reduce state space?
  - Example: SYMMETRY SymmetrySet

[pass/warn/fail] State constraints
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
-> Run: $tla-symbols <SPEC_PATH>
<endif>

<if CONSTANTS non-empty and no config>
-> Assign constant values in .cfg file
<endif>

<if SMOKE_VIOLATIONS>
-> Fix violations found in smoke test
-> Run: $tla-check for full counterexample
<endif>

<if SMOKE_SUCCESS or SMOKE_SKIPPED>
-> Run: $tla-check for exhaustive verification
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

Below is a brief example of a populated review report:

```
═══════════════════════════════════════════════════════════
TLA+ SPECIFICATION REVIEW
═══════════════════════════════════════════════════════════

Spec: test-specs/Counter.tla

─────────────────────────────────────────────────────────
1. SYNTAX & SEMANTICS (SANY Parser)
─────────────────────────────────────────────────────────
Parsing successful. No syntax errors.

─────────────────────────────────────────────────────────
2. STRUCTURE ANALYSIS (Symbol Extraction)
─────────────────────────────────────────────────────────
Constants: MaxValue
Variables: count
Init: Init
Next: Next
Spec: Spec
Invariants: TypeInvariant, BoundInvariant
Properties: None

─────────────────────────────────────────────────────────
3. SMOKE TEST (3-second simulation)
─────────────────────────────────────────────────────────
Smoke test passed
  CFG used: test-specs/Counter.cfg
  No violations found in random simulation

─────────────────────────────────────────────────────────
4. BEST PRACTICES CHECKLIST
─────────────────────────────────────────────────────────
[pass] Type invariants defined (TypeInvariant)
[pass] Safety invariants defined (BoundInvariant)
[warn] No liveness properties defined
[warn] No module header comment

─────────────────────────────────────────────────────────
5. RECOMMENDATIONS
─────────────────────────────────────────────────────────
-> Consider adding liveness properties if applicable
-> Add a module header comment explaining purpose
-> Run: $tla-check for exhaustive verification

═══════════════════════════════════════════════════════════
REVIEW COMPLETE
═══════════════════════════════════════════════════════════
```
