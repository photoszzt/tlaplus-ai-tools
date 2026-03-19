# TLA+ Model Checking Reference

This reference provides detailed educational content for TLC model checking. It is loaded on demand by the `/tla-model-checking` orchestrator skill when the user asks for details about configuration syntax, performance tuning, debugging, or best practices.

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

**Symmetric sets** (reduces state space). The set must be declared as model values for symmetry to work:

```
CONSTANT
    Servers = {s1, s2, s3}
    Clients = {c1, c2, c3}

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

Define the temporal formula in the `.tla` file:

```tla
Spec == Init /\ [][Next]_vars /\ WF_vars(Action)
```

Then in the `.cfg` file, reference it by name:

```
SPECIFICATION Spec
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

## Starting with Small Constants

Use small values initially:

- Sets: 2-3 elements
- Numbers: 3-10
- Sequences: length 3-5

**Why**: Easier debugging, faster checking, catch bugs early.

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

Use multiple cores by passing the `workers` parameter via the MCP tool's `workers` field (or the `--workers` flag in `/tla-check`):

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

For a systematic approach to debugging invariant and property violations, use `/tla-debug-violations`. It provides a step-by-step workflow for minimizing configurations, isolating failures, and analyzing counterexample traces.

You can also use the trace-analyzer agent to get explanations of what failed, why, and how to fix it.

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

### Related Skills

- `tla-getting-started` - TLA+ basics
- `tla-debug-violations` - Debug counterexamples
- `/tla-parse` - Syntax check
- `/tla-symbols` - Generate config
- `/tla-smoke` - Quick test
- `/tla-check` - Full check
- `/tla-review` - Comprehensive review

### Related Agents

- `trace-analyzer` - Analyze violations

### Knowledge Base Articles

- [tla-indentation.md](resource://knowledgebase/tla-indentation.md) - Proper TLA+ indentation
- [tla-functions-operators.md](resource://knowledgebase/tla-functions-operators.md) - Operators and functions
- [tla-functions-records-sequences.md](resource://knowledgebase/tla-functions-records-sequences.md) - Data structures
- [tla-extends-instance.md](resource://knowledgebase/tla-extends-instance.md) - Module dependencies
