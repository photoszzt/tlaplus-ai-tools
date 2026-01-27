---
name: tla-check
description: Run exhaustive model checking on TLA+ specification with TLC
argument-hint: "@spec.tla [config.cfg] [--workers N]"
allowed-tools: [Read, Bash, Grep, Write]
---

# Run TLC Model Checking

Execute exhaustive model checking on TLA+ specifications using the TLC model checker.

## Usage

```
/tla-check @Counter.tla
/tla-check @Counter.tla Counter.cfg
/tla-check @Counter.tla --workers 4
/tla-check @Spec.tla MyConfig.cfg --workers 8
```

## Arguments

- **spec.tla** (required) - TLA+ specification file
- **config.cfg** (optional) - TLC configuration file (auto-detected if omitted)
- **--workers N** (optional) - Number of worker threads (default: CPU cores)
- **--depth N** (optional) - Maximum search depth

## What This Command Does

1. Locates specification and config files
2. Validates config file exists (or finds default)
3. Invokes TLC via MCP tool `tlaplus_mcp_tlc_check`
4. Streams output in real-time
5. Reports results (success or counterexample)

## Auto-Config Detection

If no config file specified, searches for:
1. `SpecName.cfg` (same name as .tla file)
2. `MCSpecName.cfg` (model checking config)
3. `MC.cfg` (generic config)

If no config found, suggests running `/tla-symbols` to generate one.

## Output

### Success
```
TLC Model Checker
Parsing file Counter.tla
Semantic processing of module Counter
Starting state space exploration
Finished computing initial states: 1 distinct state
Finished state space exploration: 11 states, 10 transitions

Model checking completed. No errors found.
States explored: 11
Time: 0.5 seconds
```

### Invariant Violation
```
Error: Invariant BoundInvariant is violated.
State trace:
  1: count = 0
  2: count = 1
  ...
  11: count = 11  <- Invariant violated here

Use /tla-review to analyze the counterexample.
```

### Property Violation
```
Error: Temporal property Liveness is violated.
Counterexample trace shows infinite behavior.

Consider:
- Adding fairness conditions (WF_vars or SF_vars)
- Checking for deadlocks
- Reviewing temporal formula

Use tla-debug-violations skill for systematic debugging.
```

## When to Use

- **After parsing** - Validate spec correctness with `/tla-parse` first
- **Full verification** - Exhaustive state space checking
- **Before deployment** - Verify all properties hold
- **After changes** - Recheck after modifying spec
- **Finding bugs** - Discover invariant violations

## Performance Options

### Worker Threads
```
/tla-check @Spec.tla --workers 8
```
Use more workers for faster checking on multi-core systems.

### Depth Limit
```
/tla-check @Spec.tla --depth 100
```
Limit search depth for large state spaces.

### State Space Constraints
Add to .cfg file:
```
CONSTRAINT count <= 1000
```

## Interpreting Results

### No Errors Found
✅ All invariants hold for explored state space
✅ All properties satisfied
✅ Spec is correct (within model bounds)

### Counterexample Found
❌ Trace shows path to violation
❌ Review state values at each step
❌ Identify which action caused violation

### State Space Too Large
⚠️ May not finish in reasonable time
⚠️ Reduce constants in .cfg file
⚠️ Add state constraints
⚠️ Use `/tla-smoke` for quick testing

## Tips

- **Start small** - Use small constant values initially
- **Smoke test first** - Run `/tla-smoke` before full check
- **Watch memory** - TLC can use significant RAM for large state spaces
- **Use symmetry** - Define symmetry sets in config to reduce states
- **Incremental checking** - Check invariants before properties

## Error Handling

**Config not found**:
```
Error: No configuration file found for Counter.tla
Suggestion: Run /tla-symbols @Counter.tla to generate one
```

**Parse errors**:
```
Error: Specification has syntax errors
Suggestion: Run /tla-parse @Counter.tla first
```

**Java memory error**:
```
Error: Java heap space exhausted
Suggestion: Add to config: -Xmx4096m for 4GB heap
```

## Related Commands

- `/tla-parse` - Validate syntax before checking
- `/tla-smoke` - Quick 3-second test
- `/tla-symbols` - Generate configuration file
- `/tla-review` - Comprehensive spec review

## Related Skills

- `tla-model-checking` - Complete TLC workflow guide
- `tla-debug-violations` - Debug counterexamples

## Implementation

Call MCP tool with appropriate options:

```javascript
tlaplus_mcp_tlc_check({
  fileName: absolutePath,
  cfgFile: configPath,
  extraOpts: ['-workers', workerCount],
  extraJavaOpts: ['-Xmx4096m']
})
```

Stream output to user in real-time. Parse results and provide contextual suggestions based on error type.
