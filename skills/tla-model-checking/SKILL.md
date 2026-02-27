---
name: tla-model-checking
description: This skill should be used when the user asks to "model check", "run TLC", "verify specification", "check invariants", "configure TLC", "write config file", or mentions model checking workflow and TLC configuration.
version: 1.0.0
---

# TLA+ Model Checking with TLC

This skill provides comprehensive guidance for model checking TLA+ specifications using the TLC model checker.

## When to Use

- Setting up model checking for a specification
- Writing or updating TLC configuration files
- Running exhaustive model checking
- Interpreting TLC output and results
- Tuning performance for large state spaces
- Troubleshooting model checking issues

## Model Checking Workflow

### 1. Prepare Specification

Ensure specification is ready:
- Parse successfully with SANY (`/tla-parse`)
- All symbols defined
- Init and Next properly structured
- Invariants defined

### 2. Create Configuration File

Generate or write `.cfg` file with `/tla-symbols` command.

**Configuration sections**:
- Constants (assign values)
- Specification (INIT/NEXT or SPEC)
- Invariants (safety properties)
- Properties (temporal formulas)
- Constraints (optional limits)

See `references/config-guide.md` for complete configuration syntax.

### 3. Start with Small Constants

Use small values initially:
- Sets: 2-3 elements
- Numbers: 3-10
- Sequences: length 3-5

**Why**: Easier debugging, faster checking, catch bugs early.

### 4. Run Smoke Test First

Quick validation before full check:
```
/tla-smoke @Spec.tla
```
Finds obvious bugs in seconds.

### 5. Run Full Model Check

Exhaustive verification:
```
/tla-check @Spec.tla
```
Explores all reachable states.

### 6. Interpret Results

**Success**: Specification correct (within model bounds)
**Violation**: Counterexample shows bug - use trace-analyzer agent

### 7. Iterate

- Fix bugs
- Increase constants
- Add more properties
- Re-check

## TLC Configuration Files

### Basic Structure

```
\* Configuration for SpecName

CONSTANT
    MaxValue = 10
    NumProcesses = 3

SPECIFICATION Spec

INVARIANT
    TypeInvariant
    SafetyProperty

PROPERTY
    LivenessProperty
```

### Constants Section

**Ordinary values**:
```
CONSTANT
    N = 5
    MaxRetries = 3
    Timeout = 100
```

**Sets of model values**:
```
CONSTANT
    Servers = {s1, s2, s3}
    MessageTypes = {req, resp, ack}
```

**Sets of numbers**:
```
CONSTANT
    Clients = 1..3
    Priorities = {1, 2, 3}
```

**Symmetric sets** (reduces state space):
```
SYMMETRY Servers
SYMMETRY Clients
```

### Specification Section

**Option 1: Use Spec formula**:
```
SPECIFICATION Spec
```
Use when spec has temporal formula defined.

**Option 2: Separate Init/Next**:
```
INIT Init
NEXT Next
```
Use when no Spec formula or need custom temporal formula.

**With fairness**:
```
SPECIFICATION Init /\ [][Next]_vars /\ WF_vars(Action)
```

### Invariants

Properties that must hold in every reachable state:

```
INVARIANT
    TypeInvariant     \* Check types
    SafetyProperty    \* Check safety
    BoundInvariant    \* Check bounds
```

**No primed variables** in invariants - they check current state only.

### Temporal Properties

Liveness and other temporal formulas:

```
PROPERTY
    EventuallyCompletes    \* <>P - eventually P
    AlwaysResponds         \* [](Request => <>Response)
    StableState            \* <>[]P - eventually always P
```

Require fairness conditions to hold.

### State Constraints

Limit state space exploration:

```
CONSTRAINT
    queueSize <= 10
    numMessages <= 50
```

Useful for large/infinite state spaces.

### Action Constraints

Restrict which actions can execute:

```
ACTION_CONSTRAINT
    AllowedActions
```

Explores subset of behaviors.

### View Definitions

Define state equivalence:

```
VIEW ViewFunction
```

Reduces state space by treating equivalent states as identical.

## Running Model Checking

### Using Commands

**Quick test**:
```
/tla-smoke @Spec.tla
```

**Full check**:
```
/tla-check @Spec.tla
```

**With custom config**:
```
/tla-check @Spec.tla MyConfig.cfg
```

**With options**:
```
/tla-check @Spec.tla --workers 8
```

### Using MCP Tools Directly

```javascript
// Parse first
tlaplus_mcp_sany_parse({ fileName: "/path/to/Spec.tla" })

// Model check
tlaplus_mcp_tlc_check({
  fileName: "/path/to/Spec.tla",
  cfgFile: "/path/to/Config.cfg",
  extraOpts: ["-workers", "4"],
  extraJavaOpts: ["-Xmx4096m"]
})

// Smoke test
tlaplus_mcp_tlc_smoke({
  fileName: "/path/to/Spec.tla"
})
```

## Interpreting Results

### Successful Check

```
Model checking completed. No errors found.
States examined: 1,247
Distinct states: 892
Time: 2.5 seconds
```

**Means**: All invariants hold, all properties satisfied (within model bounds).

**Next steps**:
- Increase constants to check larger models
- Add more properties
- Add liveness checking

### Invariant Violation

```
Invariant BoundInvariant is violated.

State trace (length 5):
  State 1: <Initial>
  State 2: <Action: Increment>
  State 3: <Action: Increment>
  State 4: <Action: Increment>
  State 5: <Action: Increment>
    count = 11  <- Invariant violated
```

**Means**: Found state where invariant false.

**Next steps**:
1. Analyze trace with trace-analyzer agent
2. Identify which action caused violation
3. Fix the bug (strengthen guard, fix logic)
4. Re-check

### Property Violation

```
Temporal property LivenessProperty is violated.

Behavior shows stuttering at state:
  count = 10
  status = "done"
```

**Means**: Liveness property can fail.

**Common causes**:
- Missing fairness (add WF or SF)
- Deadlock (no enabled actions)
- Incorrect formula (review temporal logic)

### State Space Explosion

```
After 1 hour:
  States examined: 15,234,891
  Queue size: 8,423,112
  Memory: 3.8 GB
```

**Means**: State space too large to check completely.

**Solutions**:
- Reduce constants
- Add state constraints
- Use symmetry sets
- Increase memory
- Consider different modeling approach

## Performance Tuning

### Worker Threads

Use multiple cores:
```
/tla-check @Spec.tla --workers 8
```

**Guidelines**:
- Use number of CPU cores
- Diminishing returns beyond 8-12
- Monitor CPU usage

### Java Heap Size

Increase memory for large state spaces:
```
Add to config or use extraJavaOpts:
-Xmx8192m   (8 GB heap)
-Xmx16384m  (16 GB heap)
```

**Guidelines**:
- Start with 4 GB
- Increase if "OutOfMemoryError"
- Leave room for OS

### State Constraints

Limit exploration:
```
CONSTRAINT
    depth <= 20
    queueSize <= 100
```

**Use when**:
- Infinite state space
- Very large finite space
- Focused testing

### Symmetry Sets

Reduce states by symmetry:
```
CONSTANT Servers = {s1, s2, s3}
SYMMETRY Servers
```

**Effective when**:
- Processes/servers interchangeable
- Order doesn't matter
- Can reduce space exponentially

### View Definitions

Abstract away irrelevant details:
```
View == <<count, status>>  \* Ignore timestamp
```

**Use when**:
- Some variables don't affect correctness
- Can define equivalence classes

## Debugging Failed Checks

### Use Systematic Approach

From `tla-debug-violations` skill:

1. **Minimize configuration** - Smallest constants
2. **Check invariants only** - Remove properties temporarily
3. **Fix invariants first** - Easier than properties
4. **Add properties back** - One at a time
5. **Increase constants** - Once passing

### Analyze Traces

Use trace-analyzer agent:
```
After violation, ask:
"Analyze this counterexample"
```

Agent explains:
- What failed
- Why it failed
- How to fix

### Add Intermediate Invariants

Help narrow down bugs:
```
INVARIANT
    Step1Complete => Step2Ready
    ProcessingMsg => MsgInQueue
```

Catch issues earlier in trace.

## Best Practices

### Start Simple

- Small constants
- Type invariants only
- Basic config

Then add:
- More invariants
- Larger constants
- Temporal properties
- Fairness conditions

### Check Incrementally

After each spec change:
```
1. Parse
2. Smoke test
3. Full check (small model)
4. Full check (larger model)
```

### Use Version Control

Commit working configs:
```
Spec-Small.cfg   (quick testing)
Spec-Medium.cfg  (thorough testing)
Spec-Large.cfg   (comprehensive)
```

### Document Configuration

Add comments to `.cfg`:
```
\* These constants chosen because...
\* This constraint needed to avoid...
\* Known limitation: doesn't check...
```

### Monitor Progress

For long checks:
- Watch state count
- Check memory usage
- Estimate completion time

## Common Issues

### "No behavior satisfies Init"

**Problem**: Init predicate is unsatisfiable or constants make it impossible.

**Fix**: Check constant values, verify Init logic.

### "Deadlock reached"

**Problem**: Reached state with no enabled actions (if not intended).

**Fix**: Add termination action or check guards.

### "Java heap space"

**Problem**: Out of memory.

**Fix**: Increase -Xmx, reduce constants, add constraints.

### "Config file not found"

**Problem**: Missing `.cfg` file.

**Fix**: Run `/tla-symbols` to generate one.

## Additional Resources

### Reference Files

- **`references/config-guide.md`** - Complete configuration syntax
- **`references/performance-tuning.md`** - Optimization strategies
- **`references/temporal-logic.md`** - Temporal formula patterns

### Example Configs

- **`examples/Counter.cfg`** - Simple configuration
- **`examples/Advanced.cfg`** - Complex configuration with all options

### Related Skills

- `tla-getting-started` - TLA+ basics
- `tla-debug-violations` - Debug counterexamples
- `tla-spec-review` - Review before checking

### Related Commands

- `/tla-parse` - Syntax check
- `/tla-symbols` - Generate config
- `/tla-smoke` - Quick test
- `/tla-check` - Full check
- `/tla-review` - Comprehensive review

### Related Agents

- `spec-validator` - Automated validation
- `config-generator` - Generate configs
- `trace-analyzer` - Analyze violations

## Quick Reference

```
# Workflow
1. /tla-parse @Spec.tla          # Check syntax
2. /tla-symbols @Spec.tla         # Generate config
3. Edit Spec.cfg                  # Set constants
4. /tla-smoke @Spec.tla           # Quick test
5. /tla-check @Spec.tla           # Full check

# Config sections
CONSTANT ...      # Set values
SPECIFICATION ... # What to check
INVARIANT ...     # Safety properties
PROPERTY ...      # Temporal properties
CONSTRAINT ...    # Limit states
SYMMETRY ...      # Reduce states

# Common options
--workers N       # Parallel checking
-Xmx4096m        # Memory limit
```

Model checking is iterative - start small, check often, and grow confidence incrementally.
