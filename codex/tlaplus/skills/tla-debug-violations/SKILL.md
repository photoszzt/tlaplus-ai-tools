---
name: tla-debug-violations
description: >-
  This skill provides a systematic workflow to isolate and diagnose TLA+ invariant or property violations.
  It should be used when the user mentions "invariant violated", "TLC found a bug",
  "counterexample", "property failed", "violation trace", "debugging TLA+ violations",
  "error trace", "why did TLC fail", "fix my spec", "TLC error", "trace analysis",
  "deadlock found", or "lasso-shaped counterexample".
version: 1.0.0
---

# Debugging TLA+ Property Violations

Use this skill when TLC reports invariant or property violations to systematically diagnose the issue.

**IMPORTANT: Always use the TLA+ MCP tools named in this skill. Never fall back to running Java or TLC commands via Bash.**

## When to Use

- TLC reports an invariant violation
- TLC reports a property (liveness) violation
- Model checking fails with counterexample
- Need to understand why a spec violates requirements

## Debugging Workflow

### Step 0: Read the Spec and Config

Before debugging, read both the `.tla` spec file and its `.cfg` config file to understand:

- What variables and constants are defined
- What invariants and properties are being checked
- What the Spec formula looks like (Init, Next, fairness)

This context is essential for interpreting counterexample traces.

### Step 1: Minimize the TLC Configuration

Start with the smallest possible configuration to isolate the issue:

- Reduce the number of workers to 1
- Minimize constant values (e.g., if `N` is a constant, try `N = 2` first)
- Reduce state space constraints
- Disable symmetry sets temporarily

**Goal**: Get a fast, reproducible counterexample.

### Step 2: Remove PROPERTY Entries

Edit the `.cfg` file and temporarily remove all `PROPERTY` entries:

Before (with property):

```
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT SafetyInvariant
PROPERTY LivenessProperty
```

After (property removed):

```
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT SafetyInvariant
```

**Why**: TLC configuration files (.cfg) do not support comments, so you must remove the line entirely (you can re-add it later).

### Step 3: Check Invariants First

Run TLC with only invariants enabled:

Call `mcp__tlaplus__tlaplus_mcp_tlc_check` with `fileName` set to the spec path and `cfgFile` set to the minimal config path.

**If invariants fail**:

- Focus on the invariant violation first
- Examine the counterexample trace
- Invariants are easier to debug than liveness properties
- Fix invariant violations before checking properties

**If invariants pass**:

- Your safety properties are correct
- The issue is with liveness properties
- Use `mcp__tlaplus__tlaplus_mcp_tlc_explore` to generate specific behavior traces that help visualize the problematic execution path
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

- `mcp__tlaplus__tlaplus_mcp_tlc_check`: Run model checker with config
- `mcp__tlaplus__tlaplus_mcp_tlc_explore`: Explore state space interactively
- `mcp__tlaplus__tlaplus_mcp_sany_parse`: Verify syntax after fixes

## Tips

- **Start small**: Minimize constants and state space
- **One thing at a time**: Debug invariants before properties
- **Read the trace**: TLC's counterexample shows the path to violation
- **Add intermediate invariants**: Help narrow down where things go wrong

## Further Reading

- **`references/debugging-strategies.md`** - Advanced debugging strategies and techniques, including trace analysis, Print debugging, and common bug patterns
