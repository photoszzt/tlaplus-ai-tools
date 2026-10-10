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

All forms work identically. See `codex/tlaplus/shared/path-normalization.md` for path normalization rules.

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

Apply the CFG Selection Algorithm documented in `codex/tlaplus/shared/cfg-selection-algorithm.md`.

**Step 6: Call MCP Tool**

Invoke TLC trace exploration:

```
mcp__tlaplus__tlaplus_mcp_tlc_explore
  --fileName "<SPEC_PATH>"
  --cfgFile "<FINAL_CFG>"
  --behaviorLength <LENGTH>
```

**Step 7: Report Results**

Inspect `isError`, exit code, and TLC output before interpreting the trace.
The tool injects `-invlevel <LENGTH>` to print a trace when the requested level
is reached. A violation of that generated `TLCGet("level") < LENGTH` invariant
is expected trace termination; describe it as a sampled behavior. TLC names this
invariant `__DebuggerExpr__<number>`. Confirm it is the length invariant rather
than another injected `-inv` expression or a configured user invariant. Never dismiss a
violation of a configured user invariant or property. If its identity is unclear,
report that uncertainty.

Report parser/config failures, timeouts, cancellation, or resource failures as
incomplete exploration, preserving any partial trace without claiming success.

Print summary:

```
Spec path: <SPEC_PATH>
CFG used: <FINAL_CFG>
Behavior length: <LENGTH> steps

<TLC trace output>

Trace exploration complete.
```

If a user invariant/property violation or deadlock is found during exploration:

- Print `Violation detected during trace exploration. See counterexample above.`
- Suggest: `Use $tla-debug-violations to analyze the violation.`

If a trace was generated and only the injected length invariant stopped exploration,
or the simulation completed successfully without user violations:

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
