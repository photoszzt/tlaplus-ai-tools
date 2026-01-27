---
name: tla-smoke
description: Run quick smoke test using random simulation (3 seconds)
argument-hint: "@spec.tla [duration]"
allowed-tools: [Read, Bash, Grep]
---

# Quick Smoke Test

Run a fast smoke test using TLC's random simulation mode to quickly find violations without exhaustive state exploration.

## Usage

```
/tla-smoke @Counter.tla
/tla-smoke @Spec.tla 5
/tla-smoke @System.tla 10
```

## Arguments

- **spec.tla** (required) - TLA+ specification file
- **duration** (optional) - Test duration in seconds (default: 3)

## What This Command Does

1. Runs TLC in simulation mode (random state exploration)
2. Generates random behaviors for specified duration
3. Checks invariants on each generated state
4. Reports violations immediately if found
5. Completes quickly even for large state spaces

## How It Works

Unlike exhaustive model checking (`/tla-check`), smoke testing:
- ✅ Uses **random simulation** instead of exhaustive search
- ✅ Completes in seconds, not minutes/hours
- ✅ Good for **quick validation** during development
- ✅ Finds **common bugs** fast
- ❌ **Not exhaustive** - may miss rare bugs
- ❌ No guarantees of correctness

## When to Use

### During Development
- After each spec change
- Before committing code
- Quick sanity check
- Rapid iteration

### Before Full Check
- Pre-screen before `/tla-check`
- Find obvious bugs first
- Save time on broken specs

### Exploratory Testing
- Understand spec behavior
- Generate example traces
- Explore state space quickly

### CI/CD Pipelines
- Fast pre-commit checks
- Quick validation gates
- Complement full model checking

## Output

### Success (No Violations)
```
Running smoke test (3 seconds)...
Generated 1,247 states
Checked 1,247 states
No invariant violations found in 3 seconds

Note: This is not exhaustive verification.
Run /tla-check for complete model checking.
```

### Violation Found
```
Invariant violation found after 1.2 seconds!

Invariant BoundInvariant violated:
  count = 11 (expected <= 10)

State trace:
  1: count = 0
  2: count = 5
  3: count = 11  <- Violation

Smoke test found a bug quickly!
Fix the issue and run /tla-check for full verification.
```

### No Config File
```
No configuration file found.
Using specification defaults for smoke test.
Run /tla-symbols to generate proper config.
```

## Comparison with /tla-check

| Feature | /tla-smoke | /tla-check |
|---------|------------|------------|
| Mode | Random simulation | Exhaustive search |
| Time | 3-10 seconds | Minutes to hours |
| Coverage | Random sample | All reachable states |
| Guarantees | None | Complete verification |
| Use case | Quick testing | Final verification |

## Duration Guidelines

- **3 seconds** (default) - Quick check during editing
- **5 seconds** - More thorough, still fast
- **10 seconds** - Good balance for complex specs
- **30+ seconds** - Approaching exhaustive check time

## Tips

### Use in Workflow
```
1. Edit spec
2. /tla-smoke (3 sec) - catch obvious bugs
3. Continue editing or...
4. /tla-check (complete) - full verification
```

### Fast Iteration
```
/tla-smoke @Spec.tla && git commit
```
Quick validation before commit.

### Longer Tests
```
/tla-smoke @Spec.tla 30
```
More coverage when quick check passes.

### Watch for Patterns
If smoke test finds bugs:
- Fix the bug
- Re-run smoke test
- Once passing, do full check

If smoke test passes:
- Likely correct (but not certain)
- Run `/tla-check` for guarantee

## Limitations

### May Miss Rare Bugs
Random simulation might not explore:
- Corner cases
- Rare event sequences
- Deep state space regions
- Specific interleavings

### Not for Certification
Don't rely on smoke tests alone for:
- Safety-critical systems
- Security properties
- Compliance requirements
- Production deployment

Always follow up with `/tla-check` for formal verification.

## Related Commands

- `/tla-parse` - Syntax check before smoke test
- `/tla-check` - Exhaustive verification after smoke test
- `/tla-symbols` - Generate configuration
- `/tla-review` - Review spec structure

## Related Skills

- `tla-model-checking` - Complete TLC workflow
- `tla-debug-violations` - Debug found violations

## Implementation

Call MCP tool in simulation mode:

```javascript
tlaplus_mcp_tlc_smoke({
  fileName: absolutePath,
  cfgFile: configPath,
  extraOpts: ['-simulate', `-depth ${duration * 1000}`]
})
```

Parse output for violations and present clear results. Remind users this is not exhaustive verification.
