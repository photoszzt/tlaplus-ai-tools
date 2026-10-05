---
name: tla-explore
description: >-
  This skill generates example behavior traces from a TLA+ specification using TLC simulation.
  This skill should be used when the user asks to "explore states", "generate trace",
  "show me a behavior", "example execution", "trace exploration",
  "what happens when", "simulate", "run a simulation", "sample behavior",
  "show example states", "walk through the spec", "run an example",
  or wants to see how a spec executes step by step.
version: 1.0.0
---

# TLC Trace Exploration

Generate example behavior traces from your TLA+ specification using TLC simulation.

**IMPORTANT: Always use the TLA+ MCP tools named in this skill. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
$tla-explore test-specs/Counter.tla
$tla-explore test-specs/Counter.tla test-specs/Counter.cfg
$tla-explore test-specs/Counter.tla --length 20
```

All forms work identically. See `shared/path-normalization.md` for path normalization rules.

## What This Does

1. Validates and normalizes the spec path from the argument
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `mcp__tlaplus__tlaplus_mcp_tlc_explore` to generate a behavior trace
4. Reports the trace (sequence of states)

## Implementation

**Step 1: Normalize Spec Path**

Take the spec file path provided as the argument to this skill. If it starts with `@`, strip the leading `@`.

Print `Spec path: <spec_path>`

**Step 2: Validate File**

- Check path ends with `.tla`
- Read the file to verify the file exists on disk
- If validation fails, print error and exit

**Step 3: Parse Flags**

Extract `--length <N>` from the argument:

- Default: `LENGTH=10`
- If `--length <N>` present: `LENGTH=<N>`
- Validate `<N>` is a positive integer

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Step 5: Apply CFG Selection Algorithm**

Apply the CFG Selection Algorithm documented in `shared/cfg-selection-algorithm.md`.

**Step 6: Call MCP Tool**

Invoke TLC trace exploration:

```
mcp__tlaplus__tlaplus_mcp_tlc_explore
  --fileName "<SPEC_PATH>"
  --cfgFile "<FINAL_CFG>"
  --behaviorLength <LENGTH>
```

**Step 7: Report Results**

Print summary:

```
Spec path: <SPEC_PATH>
CFG used: <FINAL_CFG>
Behavior length: <LENGTH> steps

<TLC trace output>

Trace exploration complete.
```

If violations found during exploration:

- Print `Violation detected during trace exploration. See counterexample above.`
- Suggest: `Use $tla-debug-violations to analyze the violation.`

If no violations:

- Print `Trace generated successfully. <N> states explored.`
- Suggest: `Use $tla-check for exhaustive verification.`

## Example Output

```
Spec path: test-specs/Counter.tla
Phase 1: Spec.cfg exists
Phase 2: Using default Spec.cfg
CFG used: test-specs/Counter.cfg
Behavior length: 10 steps

State 1: <Initial state>
  count = 0

State 2:
  count = 1

State 3:
  count = 2

...

Trace generated successfully. 10 states explored.
```
