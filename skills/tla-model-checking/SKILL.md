---
name: tla-model-checking
description: >-
  This skill orchestrates the full model checking workflow: parse, configure, smoke test, and exhaustive check.
  It should be used when someone asks to "model check", "run TLC",
  "verify specification", "check invariants", "configure TLC", "write config file",
  "full verification workflow", "end-to-end TLC",
  or mentions model checking workflow and TLC configuration.
version: 3.0.0
allowed-tools:
  - Read
  - Write
  - Grep
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke
  - mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check
---

# TLA+ Model Checking Workflow

Orchestrate the full model checking workflow: parse, configure, smoke test, and exhaustive check.

**IMPORTANT: Always use the MCP tools listed above. Never fall back to running Java or TLC commands via Bash.**

**Reference**: For detailed educational content on TLC configuration syntax, performance tuning, debugging, and best practices, read `skills/tla-model-checking/reference.md` on demand.

## Usage

```
/tla-model-checking @Counter.tla
/tla-model-checking specs/MySpec.tla
```

Both forms work identically. See `skills/shared/path-normalization.md` for path normalization rules.

## Implementation

**Step 1: Validate Argument**

If no spec file path argument is provided, print `Error: No file path provided. Usage: /tla-model-checking <path.tla>` and stop.

Strip any leading `@` from the argument to get `SPEC_PATH`. Print `Spec: <SPEC_PATH>`.

**Step 2: Parse with SANY**

Read the file first to confirm it exists and ends with `.tla`.

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` with `fileName` set to `SPEC_PATH`.

- If parsing fails: print the errors to the user and **stop**. Do not proceed.
- If parsing succeeds: print `Parse: OK` and continue.

**Step 3: Check for Config File**

Derive `CFG_PATH` by replacing `.tla` with `.cfg` in `SPEC_PATH`.

Use Read to check if `CFG_PATH` exists.

If the `.cfg` file does NOT exist:

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol` with `fileName` set to `SPEC_PATH` and `includeExtendedModules` set to `false`.

Generate a `.cfg` file based on the extracted symbols (init, next, spec, invariants, properties, constants). Use the bestGuess fields from the symbol result to populate SPECIFICATION/INIT/NEXT, INVARIANT, and PROPERTY sections. Add commented stubs for any constants that need values. Write the config to `CFG_PATH` using the Write tool.

- Print `Config: Generated <CFG_PATH>` and tell the user to review and edit constant values before proceeding.
- Ask the user: "Config file generated. Please review it and confirm to proceed, or edit it first."
- Wait for user confirmation before continuing.

If the `.cfg` file already exists: print `Config: Found <CFG_PATH>` and continue.

**Step 4: Apply CFG Selection Algorithm**

Apply the CFG Selection Algorithm documented in `skills/shared/cfg-selection-algorithm.md`.

Store the final cfg path in `FINAL_CFG`.

**Step 5: Smoke Test**

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke` with:

- `fileName` set to `SPEC_PATH`
- `cfgFile` set to `FINAL_CFG`
- `extraJavaOpts` set to `["-Dtlc2.TLC.stopAfter=3"]`

- If violations found: report them to the user and ask "Smoke test found violations. Would you like to proceed to full model check anyway, or fix the issues first?"
- If no violations: print `Smoke test: Passed` and continue.

**Step 6: Full Model Check**

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check` with:

- `fileName` set to `SPEC_PATH`
- `cfgFile` set to `FINAL_CFG`

Report: total states explored, distinct states, diameter, any violations (include full counterexample traces), and final result (pass/fail).

**Step 7: Report Results**

Summarize the full workflow:

```
Model Checking Summary for <SPEC_PATH>
  Parse:      OK
  Config:     <CFG_PATH>
  Smoke test: <passed/violations found>
  Full check: <passed/violations found>

  States explored: <N>
  Distinct states: <N>
```

If violations were found, suggest: "Use `/tla-debug-violations` or the trace-analyzer agent to understand the counterexample."

If all passed, suggest: "Consider increasing constant values or adding more properties to strengthen verification."
