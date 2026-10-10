---
name: tla-check
description: >-
  This skill runs exhaustive model checking to verify all reachable states of a TLA+ specification using TLC.
  It should be used when the user asks to "check my spec", "run TLC",
  "verify my TLA+ spec", "find invariant violations", "exhaustive model checking",
  "check for bugs in my spec", "model check", "exhaustive check", "verify all states",
  "run model checker", "verify invariants", "check properties", "check temporal properties",
  "check liveness", "full check", "check all states",
  "check safety", or "verify properties".
version: 1.0.0
---

# TLC Model Checking

Run exhaustive model checking to verify all reachable states of your TLA+ specification.

**IMPORTANT: Always use the TLA+ MCP tools named in this skill. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
$tla-check test-specs/Counter.tla
$tla-check test-specs/Counter.tla test-specs/Counter.cfg
$tla-check test-specs/Counter.tla --workers 4 --heap 2G
$tla-check test-specs/Counter.tla test-specs/Counter.cfg --depth 100
```

All forms work identically. See `codex/tlaplus/shared/path-normalization.md` for path normalization rules.

## What This Does

1. Validates and normalizes the spec path from the argument
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `mcp__tlaplus__tlaplus_mcp_tlc_check` to run exhaustive model checking
4. Reports results (states explored, violations, counterexamples)

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

- `--workers <N>`: Number of worker threads (default: omit, let TLC decide)
- `--depth <N>`: Maximum search depth (default: omit)
- `--heap <SIZE>`: JVM heap size, e.g., `2G`, `1024m` (default: omit)

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Step 5: Apply CFG Selection Algorithm**

Apply the CFG Selection Algorithm documented in `codex/tlaplus/shared/cfg-selection-algorithm.md`.

**Step 6: Build MCP Tool Arguments**

Construct `extraOpts` array:

- If `WORKERS` is set: add `["-workers", "<WORKERS>"]`
- If `DEPTH` is set: add `["-depth", "<DEPTH>"]`

Construct `extraJavaOpts` array:

- If `HEAP` is set: add `["-Xmx<HEAP>"]`

**Step 7: Call MCP Tool**

Invoke TLC model checker:

```
mcp__tlaplus__tlaplus_mcp_tlc_check
  --fileName "<SPEC_PATH>"
  --cfgFile "<FINAL_CFG>"
  --extraOpts <EXTRA_OPTS>
  --extraJavaOpts <EXTRA_JAVA_OPTS>
```

**Step 8: Report Results**

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
- Suggest asking Codex to analyze the counterexample trace in detail.

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

TLC2 Version 2.18 of 10 January 2024
Running breadth-first search with 4 workers
Explored 1,234,567 states in 45 seconds
Diameter: 12 states

Model checking complete. No violations found.
All reachable states verified against invariants and properties.
```
