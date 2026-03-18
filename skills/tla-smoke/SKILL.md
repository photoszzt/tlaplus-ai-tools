---
name: tla-smoke
description: >-
  Use when the user asks for a "quick test", "fast check",
  "test my spec", "try out my spec", "smoke test", "simulate my spec",
  "random simulation", or "quick check".
version: 1.0.0
allowed-tools:
  - Read
  - Grep
  - Write
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke
---

# TLC Smoke Test

Run a quick 3-second random simulation to catch obvious bugs in your TLA+ specification.

**IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash.**

## Usage

```
/tla-smoke test-specs/Counter.tla
/tla-smoke test-specs/Counter.tla test-specs/Counter.cfg
/tla-smoke test-specs/Counter.tla --seconds 10
```

Both forms work identically --- the @ is optional and stripped during path normalization.

## What This Does

1. Validates and normalizes the spec path from the argument
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke` to run random simulation
4. Reports results (states explored, violations found)

## Implementation

**Step 1: Normalize Spec Path**

Take the spec file path provided as the argument to this skill. If it starts with `@`, strip the leading `@`.

Print `Spec path: <spec_path>`

**Step 2: Validate File**

- Check path ends with `.tla`
- Use the Read tool to verify the file exists on disk
- If validation fails, print error and exit

**Step 3: Parse Flags**

Extract `--seconds <N>` from the argument:

- Default: `SECONDS=3`
- If `--seconds <N>` present: `SECONDS=<N>`
- Validate `<N>` is a positive integer

**Step 4: Determine CFG Argument**

Parse the second token from the argument (split by space, take second). If it ends with `.cfg`, treat it as the CFG_ARG.

**Steps 5-6: Apply CFG Selection Algorithm**

Apply the CFG Selection Algorithm documented in `skills/shared/cfg-selection-algorithm.md`.

**Step 7: Call MCP Tool**

Invoke TLC smoke test:

```
mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke
  --fileName "<SPEC_PATH>"
  --cfgFile "<FINAL_CFG>"
  --extraJavaOpts ["-Dtlc2.TLC.stopAfter=<SECONDS>"]
```

**Note on `--seconds` flag:**

The MCP tool sets `-Dtlc2.TLC.stopAfter=3` by default for a 3-second simulation. When you pass `--seconds N`, an additional `-Dtlc2.TLC.stopAfter=N` is appended to `extraJavaOpts` to override this default. If the override does not take effect (runtime still ~3s), use `/tla-check` instead for thorough checking.

**Step 8: Report Results**

Print summary:

```
Spec path: <SPEC_PATH>
CFG used: <FINAL_CFG>
Smoke duration: <SECONDS> seconds (default 3s unless overridden)

<TLC output>

Smoke test complete
```

If violations found:

- Print `Violations detected. Run /tla-check for full trace.`

If no violations:

- Print `No violations found in smoke test. Run /tla-check for exhaustive verification.`

## Example Output

```
Spec path: test-specs/Counter.tla
Phase 1: Spec.cfg exists
Phase 2: Using default Spec.cfg
CFG used: test-specs/Counter.cfg
Smoke duration: 3 seconds (default 3s unless overridden)

TLC2 Version 2.18 of Day Month 20XX
Running in simulation mode with seed 1234567890
Explored 1523 states in 3 seconds

No violations found in smoke test. Run /tla-check for exhaustive verification.
```
