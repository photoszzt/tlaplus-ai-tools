# CFG Selection Algorithm

This is the canonical algorithm for selecting a TLC configuration file (`.cfg`) given a TLA+ spec path and optional CFG argument.

## Inputs

- `SPEC_PATH`: Path to the `.tla` spec file
- `CFG_ARG`: Optional explicit `.cfg` path provided by the user

## Derived Values

```
SPEC_DIR = dirname(SPEC_PATH)
SPEC_NAME = basename(SPEC_PATH, .tla)
```

## Phase 1: Ensure Precondition (a cfg exists)

Check preconditions in order:

1. If `SPEC_DIR/SPEC_NAME.cfg` exists:
   - Print `Phase 1: SPEC_NAME.cfg exists`
   - Precondition satisfied

2. Else if `SPEC_DIR/MC<SPEC_NAME>.tla` AND `SPEC_DIR/MC<SPEC_NAME>.cfg` both exist:
   - Print `Phase 1: MC pair exists (MC<SPEC_NAME>.tla + MC<SPEC_NAME>.cfg)`
   - Precondition satisfied
   - **IMPORTANT:** Do NOT create `SPEC_NAME.cfg` in this case

3. Else if `CFG_ARG` is non-empty and exists:
   - Copy `CFG_ARG` to `SPEC_DIR/SPEC_NAME.cfg` (non-clobbering: if the target file already exists, skip the copy and use the existing file)
   - Print `Phase 1: Copied cfgArg to SPEC_NAME.cfg`
   - Precondition satisfied

4. Else if `SPEC_DIR/SPEC_NAME.generated.cfg` exists:
   - Copy it to `SPEC_DIR/SPEC_NAME.cfg` (non-clobbering: if the target file already exists, skip the copy and use the existing file)
   - Print `Phase 1: Copied SPEC_NAME.generated.cfg to SPEC_NAME.cfg`
   - Precondition satisfied

5. Else:
   - Print `Error: No config file found. Run: /tla-symbols <SPEC_PATH>`
   - Exit

## Phase 2: Choose Which CFG to Pass to TLC

Determine which cfg to pass to TLC:

1. If `CFG_ARG` is non-empty:
   - Resolve `CFG_ARG` to absolute path
   - If `dirname(CFG_ARG) == dirname(SPEC_PATH)`:
     - Use `CFG_ARG` directly
     - Print `Phase 2: Using explicit cfgArg: <CFG_ARG>`
   - Else:
     - Find first available name: `SPEC_DIR/SPEC_NAME.override.cfg`, `.override.1.cfg`, `.override.2.cfg`, ...
     - Copy `CFG_ARG` to that path
     - Use the copied cfg
     - Print `Phase 2: Copied cfgArg to SPEC_NAME.override.cfg`

2. Else:
   - If `SPEC_DIR/SPEC_NAME.cfg` exists:
     - Use `SPEC_DIR/SPEC_NAME.cfg`
     - Print `Phase 2: Using default SPEC_NAME.cfg`
   - Else if `SPEC_DIR/MC<SPEC_NAME>.cfg` exists:
     - Use `SPEC_DIR/MC<SPEC_NAME>.cfg`
     - Set `SPEC_PATH` to `SPEC_DIR/MC<SPEC_NAME>.tla` (see Phase 1, step 2)
     - Print `Phase 2: Using default MC<SPEC_NAME>.cfg`
   - Else:
     - Print `Error: Unreachable state (Phase 1 should have ensured cfg exists)`
     - Exit

Store final cfg path in `FINAL_CFG`.

## Outputs

- `FINAL_CFG`: The resolved path to the `.cfg` file to pass to TLC
- `SPEC_PATH`: Potentially updated spec path (changed to `SPEC_DIR/MC<SPEC_NAME>.tla` when an MC pair is used in Phase 2)
