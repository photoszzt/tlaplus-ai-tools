---
name: tla-debug-violations
description: Use when debugging TLA+ invariant or property violations. Provides systematic workflow to isolate and diagnose issues.
---

# Debugging TLA+ Property Violations

Use this skill when TLC reports invariant or property violations to systematically diagnose the issue.

## When to Use

- TLC reports an invariant violation
- TLC reports a property (liveness) violation
- Model checking fails with counterexample
- Need to understand why a spec violates requirements

## Debugging Workflow

### Step 1: Minimize the TLC Configuration

Start with the smallest possible configuration to isolate the issue:

- Reduce the number of workers to 1
- Minimize constant values (e.g., if `N` is a constant, try `N = 2` first)
- Reduce state space constraints
- Disable symmetry sets temporarily

**Goal**: Get a fast, reproducible counterexample.

### Step 2: Remove PROPERTY Entries

Edit your `.cfg` file and temporarily remove all `PROPERTY` entries:

```
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT SafetyInvariant
# PROPERTY LivenessProperty  <- Comment out
```

**Why**: Separate invariant violations from liveness violations.

### Step 3: Check Invariants First

Run TLC with only invariants enabled:

```bash
# Use MCP tool
mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check '{"fileName": "Spec.tla", "cfgFile": "minimal.cfg"}'
```

**If invariants fail**:
- Focus on the invariant violation first
- Examine the counterexample trace
- Invariants are easier to debug than liveness properties
- Fix invariant violations before checking properties

**If invariants pass**:
- Your safety properties are correct
- The issue is with liveness properties
- Proceed to Step 4

### Step 4: Analyze Property Violations

If invariants pass but properties fail, re-enable properties one at a time:

1. Add back ONE property to the config
2. Run TLC again
3. Examine the counterexample
4. Check for:
   - Missing fairness conditions
   - Incorrect temporal formulas
   - Deadlocks preventing progress

## Common Causes of Violations

### Invariant Violations
- **Type errors**: Variable has wrong type
- **Logic errors**: Next action allows invalid transitions
- **Missing constraints**: Init or Next too permissive

### Property Violations
- **Missing fairness**: Add `WF_vars(Action)` or `SF_vars(Action)`
- **Deadlock**: Spec allows states with no outgoing transitions
- **Incorrect temporal formula**: `[]<>P` vs `<>[]P` confusion

## MCP Tools for Debugging

- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check`: Run model checker with config
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_explore`: Explore state space interactively
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse`: Verify syntax after fixes

## Tips

- **Start small**: Minimize constants and state space
- **One thing at a time**: Debug invariants before properties
- **Read the trace**: TLC's counterexample shows the path to violation
- **Add intermediate invariants**: Help narrow down where things go wrong
