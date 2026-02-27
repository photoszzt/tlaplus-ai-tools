---
name: tla-smoke
description: Run quick smoke test using random simulation (3 seconds)
argument-hint: "@spec.tla [duration]"
allowed-tools:
  [Read, Bash, Grep, mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke]
agent: build
---

# TLC Smoke Test

Run a quick 3-second random simulation to catch obvious bugs in your TLA+ specification.

## Usage

```
/tla-smoke test-specs/Counter.tla
/tla-smoke test-specs/Counter.tla test-specs/Counter.cfg
/tla-smoke test-specs/Counter.tla --seconds 10
```

**Note:** If you typed `@path.tla` as the first argument, this command strips the leading `@` and validates the file exists.

## What This Does

1. Validates and normalizes the spec path from `$ARGUMENTS`
2. Applies deterministic `.cfg` selection algorithm (see below)
3. Calls `tlaplus_mcp_tlc_smoke` to run random simulation
4. Reports results (states explored, violations found)

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

Extract `--seconds <N>` from `$ARGUMENTS`:

- Default: `SECONDS=3`
- If `--seconds <N>` present: `SECONDS=<N>`
- Validate `<N>` is a positive integer

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

**Step 7: Call MCP Tool**

Invoke TLC smoke test:

```
tlaplus_mcp_tlc_smoke \
  --fileName "$SPEC_PATH" \
  --cfgFile "$FINAL_CFG" \
  --extraJavaOpts '["-Dtlc2.TLC.stopAfter='$SECONDS'"]'
```

**Note on `--seconds` flag:**

- The MCP tool always includes `-Dtlc2.TLC.stopAfter=3` by default
- Adding another `-D` flag should override, but this is **best-effort**
- If runtime still appears ~3s with `--seconds 10`, document that OpenCode/TLC may not honor the override

**Step 8: Report Results**

Print summary:

```
Spec path: $SPEC_PATH
CFG used: $FINAL_CFG
Smoke duration: $SECONDS seconds (default 3s unless overridden)

<TLC output>

✓ Smoke test complete
```

If violations found:

- Print `✗ Violations detected. Run /tla-check for full trace.`

If no violations:

- Print `✓ No violations found in smoke test. Run /tla-check for exhaustive verification.`

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

✓ No violations found in smoke test. Run /tla-check for exhaustive verification.
```
