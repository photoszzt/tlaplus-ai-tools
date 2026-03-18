---
name: tla-check
description: >-
  Use when the user asks to "check my spec", "run TLC",
  "verify my TLA+ spec", "find invariant violations", "exhaustive model checking",
  "check for bugs in my spec", "model check", "exhaustive check", or "verify all states".
version: 1.0.0
allowed-tools:
  - Read
  - Grep
  - Write
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check
---

# TLC Model Checking

Run exhaustive model checking to verify all reachable states of your TLA+ specification.

**IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
/tla-check test-specs/Counter.tla
/tla-check test-specs/Counter.tla test-specs/Counter.cfg
/tla-check test-specs/Counter.tla --workers 4 --heap 2G
/tla-check test-specs/Counter.tla test-specs/Counter.cfg --depth 100
```

Both forms work identically --- the @ is optional and stripped during path normalization.

## What This Does

1. Validates and normalizes the spec path from the argument
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check` to run exhaustive model checking
4. Reports results (states explored, violations, counterexamples)

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

- `--workers <N>`: Number of worker threads (default: omit, let TLC decide)
- `--depth <N>`: Maximum search depth (default: omit)
- `--heap <SIZE>`: JVM heap size, e.g., `2G`, `1024m` (default: omit)

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Steps 5-6: Apply CFG Selection Algorithm**

Apply the CFG Selection Algorithm documented in `skills/shared/cfg-selection-algorithm.md`.

**Step 7: Build MCP Tool Arguments**

Construct `extraOpts` array:

- If `WORKERS` is set: add `["-workers", "<WORKERS>"]`
- If `DEPTH` is set: add `["-depth", "<DEPTH>"]`

Construct `extraJavaOpts` array:

- If `HEAP` is set: add `["-Xmx<HEAP>"]`

**Step 8: Call MCP Tool**

Invoke TLC model checker:

```
mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check
  --fileName "<SPEC_PATH>"
  --cfgFile "<FINAL_CFG>"
  --extraOpts <EXTRA_OPTS>
  --extraJavaOpts <EXTRA_JAVA_OPTS>
```

**Step 9: Report Results**

Print summary:

```
Spec path: <SPEC_PATH>
CFG used: <FINAL_CFG>
TLC options:
  Workers: <WORKERS> (or TLC default)
  Depth: <DEPTH> (or unlimited)
  Heap: <HEAP> (or JVM default)

<TLC output>
```

If violations found:

- Print `Violations detected. See counterexample above.`
- Suggest: `Use trace-analyzer agent to understand the violation.`

If no violations:

- Print `Model checking complete. No violations found.`
- Print `All reachable states verified against invariants and properties.`

If state space too large:

- Print `State space explosion detected. Consider:`
- Print `  1. Add state constraints to limit exploration`
- Print `  2. Reduce constant values`
- Print `  3. Use symmetry sets`
- Print `  4. Increase --heap size`

## Example Output

```
Spec path: test-specs/Counter.tla
Phase 1: Spec.cfg exists
Phase 2: Using default Spec.cfg
CFG used: test-specs/Counter.cfg
TLC options:
  Workers: 4
  Depth: (unlimited)
  Heap: 2G

TLC2 Version 2.18 of Day Month 20XX
Running breadth-first search with 4 workers
Explored 1,234,567 states in 45 seconds
Diameter: 12 states

Model checking complete. No violations found.
All reachable states verified against invariants and properties.
```
