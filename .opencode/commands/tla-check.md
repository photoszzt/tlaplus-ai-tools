---
name: tla-check
description: Run exhaustive model checking on TLA+ specification with TLC
argument-hint: "@spec.tla [config.cfg] [--workers N]"
allowed-tools: [Read, Bash, Grep, Write]
agent: build
---

# TLC Model Checking

Run exhaustive model checking to verify all reachable states of your TLA+ specification.

## Usage

```
/tla-check test-specs/Counter.tla
/tla-check test-specs/Counter.tla test-specs/Counter.cfg
/tla-check test-specs/Counter.tla --workers 4 --heap 2G
/tla-check test-specs/Counter.tla test-specs/Counter.cfg --depth 100
```

**Note:** If you typed `@path.tla` as the first argument, this command strips the leading `@` and validates the file exists.

## What This Does

1. Validates and normalizes the spec path from `$ARGUMENTS`
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `tlaplus_mcp_tlc_check` to run exhaustive model checking
4. Reports results (states explored, violations, counterexamples)

## Implementation

**Step 1: Normalize Spec Path**

```
SPEC_PATH="$ARGUMENTS"
if [[ "$SPEC_PATH" == @* ]]; then
  SPEC_PATH="${SPEC_PATH#@}"
fi
```

Print `Spec path: $SPEC_PATH`

**Step 2: Validate File**

- Check path ends with `.tla`
- Check file exists on disk
- If validation fails, print error and exit

**Step 3: Parse Flags**

Extract flags from `$ARGUMENTS`:
- `--workers <N>`: Number of worker threads (default: omit, let TLC decide)
- `--depth <N>`: Maximum search depth (default: omit)
- `--heap <SIZE>`: JVM heap size, e.g., `2G`, `1024m` (default: omit)

Store in variables:
```
WORKERS=""
DEPTH=""
HEAP=""
```

**Step 4: Determine CFG Argument**

```
# Parse second token from $ARGUMENTS (split by space, take second)
CFG_ARG=""
read -r FIRST_ARG SECOND_ARG REST <<< "$ARGUMENTS"
if [[ "$SECOND_ARG" == *.cfg ]]; then
  CFG_ARG="$SECOND_ARG"
fi
```

**Step 5: Apply CFG Selection Algorithm (Phase 1)**

Extract spec name and directory:
```
SPEC_DIR=$(dirname "$SPEC_PATH")
SPEC_NAME=$(basename "$SPEC_PATH" .tla)
```

Check preconditions in order:

1. If `$SPEC_DIR/$SPEC_NAME.cfg` exists:
   - Print `Phase 1: Spec.cfg exists`
   - Precondition satisfied

2. Else if `$SPEC_DIR/MC$SPEC_NAME.tla` AND `$SPEC_DIR/MC$SPEC_NAME.cfg` both exist:
   - Print `Phase 1: MC pair exists (MC$SPEC_NAME.tla + MC$SPEC_NAME.cfg)`
   - Precondition satisfied
   - **IMPORTANT:** Do NOT create `Spec.cfg` in this case

3. Else if `CFG_ARG` is non-empty and exists:
   - Copy `$CFG_ARG` to `$SPEC_DIR/$SPEC_NAME.cfg` (non-clobbering)
   - Print `Phase 1: Copied cfgArg to $SPEC_NAME.cfg`
   - Precondition satisfied

4. Else if `$SPEC_DIR/$SPEC_NAME.generated.cfg` exists:
   - Copy it to `$SPEC_DIR/$SPEC_NAME.cfg` (non-clobbering)
   - Print `Phase 1: Copied $SPEC_NAME.generated.cfg to $SPEC_NAME.cfg`
   - Precondition satisfied

5. Else:
   - Print `Error: No config file found. Run: /tla-symbols $SPEC_PATH`
   - Exit

**Step 6: Apply CFG Selection Algorithm (Phase 2)**

Determine which cfg to pass to TLC:

1. If `CFG_ARG` is non-empty:
   - Resolve `CFG_ARG` to absolute path
   - If `dirname(CFG_ARG) == dirname(SPEC_PATH)`:
     - Use `CFG_ARG` directly
     - Print `Phase 2: Using explicit cfgArg: $CFG_ARG`
   - Else:
     - Find first available name: `$SPEC_DIR/$SPEC_NAME.override.cfg`, `.override.1.cfg`, `.override.2.cfg`, ...
     - Copy `CFG_ARG` to that path
     - Use the copied cfg
     - Print `Phase 2: Copied cfgArg to $SPEC_NAME.override.cfg`

2. Else:
   - If `$SPEC_DIR/$SPEC_NAME.cfg` exists:
     - Use `$SPEC_DIR/$SPEC_NAME.cfg`
     - Print `Phase 2: Using default Spec.cfg`
   - Else if `$SPEC_DIR/MC$SPEC_NAME.cfg` exists:
     - Use `$SPEC_DIR/MC$SPEC_NAME.cfg`
     - Print `Phase 2: Using default MC$SPEC_NAME.cfg`
   - Else:
     - Print `Error: Unreachable state (Phase 1 should have ensured cfg exists)`
     - Exit

Store final cfg path in `FINAL_CFG`.

**Step 7: Build MCP Tool Arguments**

Construct `extraOpts` array:
```
EXTRA_OPTS=[]
if [[ -n "$WORKERS" ]]; then
  EXTRA_OPTS+=("-workers", "$WORKERS")
fi
if [[ -n "$DEPTH" ]]; then
  EXTRA_OPTS+=("-depth", "$DEPTH")
fi
```

Construct `extraJavaOpts` array:
```
EXTRA_JAVA_OPTS=[]
if [[ -n "$HEAP" ]]; then
  EXTRA_JAVA_OPTS+=("-Xmx$HEAP")
fi
```

**Step 8: Call MCP Tool**

Invoke TLC model checker:
```
tlaplus_mcp_tlc_check \
  --fileName "$SPEC_PATH" \
  --cfgFile "$FINAL_CFG" \
  --extraOpts $EXTRA_OPTS \
  --extraJavaOpts $EXTRA_JAVA_OPTS
```

**Step 9: Report Results**

Print summary:
```
Spec path: $SPEC_PATH
CFG used: $FINAL_CFG
TLC options:
  Workers: $WORKERS (or TLC default)
  Depth: $DEPTH (or unlimited)
  Heap: $HEAP (or JVM default)

<TLC output>
```

If violations found:
- Print `✗ Violations detected. See counterexample above.`
- Suggest: `Use trace-analyzer agent to understand the violation.`

If no violations:
- Print `✓ Model checking complete. No violations found.`
- Print `All reachable states verified against invariants and properties.`

If state space too large:
- Print `⚠ State space explosion detected. Consider:`
- Print `  1. Add state constraints to limit exploration`
- Print `  2. Reduce constant values`
- Print `  3. Use symmetry sets`
- Print `  4. Increase --heap size`

## Example Output

```
Spec path: test-specs/Counter.tla
Phase 1: Spec.cfg exists
Phase 2: Using default Spec.cfg
CFG used: test-specs/Counter.cfg
TLC options:
  Workers: 4
  Depth: (unlimited)
  Heap: 2G

TLC2 Version 2.18 of Day Month 20XX
Running breadth-first search with 4 workers
Explored 1,234,567 states in 45 seconds
Diameter: 12 states

✓ Model checking complete. No violations found.
All reachable states verified against invariants and properties.
```
