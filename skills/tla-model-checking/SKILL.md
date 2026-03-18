---
name: tla-model-checking
description: This skill should be used when the user asks to "model check", "run TLC", "verify specification", "check invariants", "configure TLC", "write config file", or mentions model checking workflow and TLC configuration.
version: 2.0.0
allowed-tools: [Read, Agent]
---

# TLA+ Model Checking Orchestrator

This skill orchestrates the full model checking workflow by spawning a sub-agent for each step. Each agent gets its own context window with only the tools it needs.

**Reference**: For detailed educational content on TLC configuration syntax, performance tuning, debugging, and best practices, read `skills/tla-model-checking/reference.md` on demand.

## Usage

```
/tla-model-checking @Counter.tla
/tla-model-checking specs/MySpec.tla
```

## Implementation

**Step 1: Validate Argument**

If no spec file path argument is provided, print `Error: No file path provided. Usage: /tla-model-checking <path.tla>` and stop.

Strip any leading `@` from the argument to get `SPEC_PATH`. Print `Spec: <SPEC_PATH>`.

**Step 2: Parse with SANY**

Spawn an Agent with this prompt:

> Parse the TLA+ specification at `<SPEC_PATH>` using the MCP tool `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` with `fileName` set to `<SPEC_PATH>`. Read the file first to confirm it exists and ends with `.tla`. Report whether parsing succeeded or failed, and include any error messages. IMPORTANT: Use ONLY the MCP tool, never run Java or TLC commands via Bash.

- If the agent reports parse failure: print the errors to the user and **stop**. Do not proceed.
- If the agent reports success: print `Parse: OK` and continue.

**Step 3: Check for Config File**

Use Read to check if a `.cfg` file exists for the spec:

- Derive `CFG_PATH` by replacing `.tla` with `.cfg` in `SPEC_PATH`
- Try to read `CFG_PATH`

If the `.cfg` file does NOT exist, spawn an Agent with this prompt:

> Extract symbols from the TLA+ specification at `<SPEC_PATH>` and generate a TLC configuration file. Use the MCP tool `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol` with `fileName` set to `<SPEC_PATH>`. Then generate a `.cfg` file based on the extracted symbols (init, next, spec, invariants, properties, constants). Write the config to `<CFG_PATH>`. Use the bestGuess fields from the symbol result to populate SPECIFICATION/INIT/NEXT, INVARIANT, and PROPERTY sections. Add commented stubs for any constants that need values. IMPORTANT: Use ONLY the MCP tool, never run Java or TLC commands via Bash.

- Print `Config: Generated <CFG_PATH>` and tell the user to review and edit constant values before proceeding.
- Ask the user: "Config file generated. Please review it and confirm to proceed, or edit it first."
- Wait for user confirmation before continuing.

If the `.cfg` file already exists: print `Config: Found <CFG_PATH>` and continue.

**Step 4: Smoke Test**

Spawn an Agent with this prompt:

> Run a TLC smoke test on the TLA+ specification at `<SPEC_PATH>` with config `<CFG_PATH>`. Use the MCP tool `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke` with `fileName` set to `<SPEC_PATH>` and `cfgFile` set to `<CFG_PATH>`. Report: number of states explored, any violations found (include full counterexample trace if present), and whether the smoke test passed. IMPORTANT: Use ONLY the MCP tool, never run Java or TLC commands via Bash.

- If violations found: report them to the user and ask "Smoke test found violations. Would you like to proceed to full model check anyway, or fix the issues first?"
- If no violations: print `Smoke test: Passed` and continue.

**Step 5: Full Model Check**

Spawn an Agent with this prompt:

> Run exhaustive TLC model checking on the TLA+ specification at `<SPEC_PATH>` with config `<CFG_PATH>`. Use the MCP tool `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check` with `fileName` set to `<SPEC_PATH>` and `cfgFile` set to `<CFG_PATH>`. Report: total states explored, distinct states, diameter, any violations (include full counterexample traces), and final result (pass/fail). IMPORTANT: Use ONLY the MCP tool, never run Java or TLC commands via Bash.

**Step 6: Report Results**

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
