# OpenCode-native `/tla-*` commands + docs alignment

## TL;DR

Ship **OpenCode custom commands** under `.opencode/commands/*.md` so OpenCode users can run:

- `/tla-parse`
- `/tla-symbols` (also writes a `.cfg`)
- `/tla-smoke`
- `/tla-check`
- `/tla-review` (full workflow, smoke-by-default)
- `/tla-setup`

Then **fix docs** (OPENCODE.md + README + INSTALLATION + TESTING) to reflect reality (OPENCODE.md is currently outdated), and add **automated Jest lint tests in CI** that validate the OpenCode command markdown files. Provide a **local-only E2E script** to run the commands via `opencode run --command`.

**Estimated Effort**: Medium

**Parallel Execution**: YES (2 waves)

**Critical Path**: Validate OpenCode command semantics → create `.opencode/commands` → update docs/tests

---

## Context

### Original Request
Align this repo with current OpenCode capabilities by shipping OpenCode-native `/tla-*` commands and updating docs. Ensure verification is automated in CI (Jest lint tests). Provide a local script for full E2E.

### Key Findings
- OpenCode **does** support custom commands invoked as `/name` and definable via `.opencode/commands/*.md`.
- This repo currently ships `.opencode/opencode.json` (MCP server config) but **no** `.opencode/commands/`.
- `OPENCODE.md` currently claims commands are not supported; it is outdated.
- MCP tools require a **real filesystem path** (`fileName`), so OpenCode command templates must treat `@path` as a path string and strip leading `@`.
- TLC tools in this repo pass **only `path.basename(cfgFile)`** to TLC while running TLC in the spec directory (see `src/tools/tlc.ts`). Therefore, any `cfgFile` used by `/tla-smoke`, `/tla-check`, `/tla-review` must be **co-located** with the `.tla` file (or must be copied there first).

### Guardrails (from review)
- Do **not** modify or remove existing Claude Code commands in `commands/`.
- Do **not** change MCP server behavior or add new MCP tools.
- Ship **only** the 6 commands agreed.
- CI automation must not require OpenCode credentials/model access.
- Ensure Windows path/quoting considerations are documented and tests avoid OS-specific assumptions.
- Do not assume OpenCode agent/tool availability without stating it explicitly.

---

## Work Objectives

### Core Objective
Make OpenCode users first-class citizens by shipping OpenCode-native `/tla-*` commands, correcting documentation, and adding CI-safe automated validation.

### Concrete Deliverables
- `.opencode/commands/tla-parse.md`
- `.opencode/commands/tla-symbols.md`
- `.opencode/commands/tla-smoke.md`
- `.opencode/commands/tla-check.md`
- `.opencode/commands/tla-review.md`
- `.opencode/commands/tla-setup.md`
- Doc updates: `OPENCODE.md`, `README.md`, `INSTALLATION.md`, `TESTING.md`
- Jest lint tests validating OpenCode command markdown and docs alignment
- Local-only E2E runner script + docs describing prerequisites and usage

### Definition of Done
- [ ] OpenCode commands are discoverable in OpenCode and follow OpenCode command spec
- [ ] Commands accept spec paths in a way that *always* yields an on-disk path for MCP tools:
  - [ ] Required: **plain path** as first argument: `path/to/spec.tla`
  - [ ] Best-effort convenience: if the user types `@path/to/spec.tla` as `$1`, the command strips the leading `@` and proceeds *only if* the result looks like a path and exists on disk; otherwise it prints a clear error and tells the user to rerun with a plain path.
- [ ] Templates and docs clearly explain that MCP tools require a filesystem path and how to provide it
- [ ] `/tla-symbols` writes a `.cfg` file (best-effort template) without clobbering existing config silently
- [ ] `/tla-review` runs parse + symbols + smoke (default) + checklist output
- [ ] Docs no longer contain the false claim “Commands not supported” for OpenCode
- [ ] `npm test` passes in CI (ubuntu/macos/windows) and includes new lint tests
- [ ] Local E2E script exists and is documented (not executed in CI)

---

## Command Contract Matrix (no ambiguity)

> This matrix is the canonical contract the implementation must follow.

### Common conventions (all commands)

- **Command name**: derived from filename under `.opencode/commands/`.
- **Argument contract (tokenized by whitespace)**:
  - `$1` = **spec filesystem path** (required)
  - Remaining tokens may be either:
    - an optional second path argument (command-specific; used by TLC commands as an explicit `.cfg` path), OR
    - flags (`--...`) and their values

- **Ordering rule (mandatory; deterministic)**:
  - Paths (`$1` and optional `$2`) must come **before** any flags.
  - Flags must come after paths.
  - If the user violates ordering, the command should print a short “Usage” and stop.

- **Quoting rule (documented limitation)**:
  - To keep parsing deterministic and cross-platform, the first implementation assumes **no spaces in paths**.
  - If users need spaces, they must rename or use paths without spaces (or validate OpenCode quoting behavior and update the contract).
- **Spec path normalization**:
  - If `$1` starts with `@`, strip the leading `@` to obtain the path candidate.
  - Before calling MCP tools, validate:
    - the resulting string ends with `.tla` (simple heuristic to avoid accidentally treating inlined content as a path)
    - the file exists on disk
  - If validation fails, print a concise error and stop.

- **What “@file support” means in this plan (no ambiguity)**:
  - Commands may accept `$1` starting with `@` *only* as a convenience for users who type it.
  - Commands must **not** depend on OpenCode expanding or preserving `@file` tokens in a particular way.
  - Whenever the command needs spec contents (for context or generation), it must explicitly **Read** the spec file at `specPath`.

- **Do not depend on OpenCode `@file` expansion**:
  - OpenCode docs describe `@file` as a template-time file inclusion mechanism. Runtime behavior when users type `@file` as an argument may vary.
  - Therefore, whenever the command needs the spec contents for context or to generate output, it must explicitly **Read** the spec file at `specPath`.
- **User-facing debug line** (mandatory): each command must print at least:
  - `Spec path: <resolved-path>`
  - For TLC commands: `CFG used: <resolved-cfg-path | none>`

### IMPORTANT: MC config behavior (must match repo TLC tools)

The repo’s TLC tools (`getSpecFiles`) attempt to auto-detect model-checking configs as:

- `<SpecBase>.cfg` next to `<SpecBase>.tla`, OR
- `MC<SpecBase>.tla` + `MC<SpecBase>.cfg`

Therefore:
- TLC commands should be invoked with the **base spec** (e.g., `Counter.tla`), not `MCounter.tla`.
- If a user passes `MCounter.tla`, the tool will look for `MCMCounter.tla`, which is almost certainly not present.

### Per-command contracts

#### `/tla-parse` → `.opencode/commands/tla-parse.md`
- MCP calls: `tlaplus_mcp_sany_parse(fileName=<spec>)`
- Output requirements:
  - print `Spec path: ...`
  - print parse result summary (success/errors)

#### `/tla-symbols` → `.opencode/commands/tla-symbols.md`
- MCP calls:
  1) `tlaplus_mcp_sany_parse(fileName=<spec>)` (fail fast on parse errors)
  2) `tlaplus_mcp_sany_symbol(fileName=<spec>, includeExtendedModules=<flag>)`

- Flags:
  - `--extended` → `includeExtendedModules=true` (default false)
- Must write cfg:
  - If `<Spec>.cfg` does not exist, write `<Spec>.cfg`.
  - Else write `<Spec>.generated.cfg` (never overwrite).
- Output requirements:
  - print `Spec path: ...`
  - print `CFG written: ...`

#### `/tla-smoke` → `.opencode/commands/tla-smoke.md`
- MCP calls: `tlaplus_mcp_tlc_smoke(fileName=<spec>, cfgFile=<cfg-or-omit>)`
- Uses cfg selection policy below.

- Optional second argument:
  - `$2` may be an explicit `.cfg` path (must end with `.cfg`)

- Flags:
  - `--seconds <N>` (integer)
    - default: 3
    - maps to MCP `extraJavaOpts: ['-Dtlc2.TLC.stopAfter=<N>']`
    - Rationale: MCP tool always includes `-Dtlc2.TLC.stopAfter=3` first (see `src/tools/tlc.ts`); adding another `-D` later should override, but treat this as **best-effort**.

- Verifiability note (must document in command text):
  - If the runtime duration still appears ~3s even with `--seconds`, document that OpenCode/TLC may not honor the override and keep default behavior.
- Output requirements:
  - print `Spec path: ...`
  - print `CFG used: ...`
  - print smoke duration semantics (default 3s unless overridden)

#### `/tla-check` → `.opencode/commands/tla-check.md`
- MCP calls: `tlaplus_mcp_tlc_check(fileName=<spec>, cfgFile=<cfg-or-omit>, extraOpts=<workers/depth>, extraJavaOpts=<heap>)`
- Uses cfg selection policy below.

- Optional second argument:
  - `$2` may be an explicit `.cfg` path (must end with `.cfg`)

- Flags:
  - `--workers <N>` → MCP `extraOpts: ['-workers', '<N>']`
  - `--depth <N>` → MCP `extraOpts: ['-depth', '<N>']`
  - `--heap <SIZE>` (e.g. `2G`, `1024m`) → MCP `extraJavaOpts: ['-Xmx<SIZE>']`

- Defaults:
  - workers: omit (let TLC decide)
  - depth: omit
  - heap: omit
- Output requirements:
  - print `Spec path: ...`
  - print `CFG used: ...`
  - print the exact TLC options used (workers/depth/heap)

#### `/tla-review` → `.opencode/commands/tla-review.md`
- Runs full workflow:
  1) parse
  2) symbols
  3) smoke (default)
  4) checklist / report

- Optional second argument:
  - `$2` may be an explicit `.cfg` path (must end with `.cfg`) and is used for the smoke step.

- Flags:
  - `--no-smoke` → skip smoke (default smoke enabled)
- Output requirements:
  - print a clear “Review Summary” section with parse/symbols/smoke outcomes and next steps.

#### `/tla-setup` → `.opencode/commands/tla-setup.md`
- Goal: guided verification steps (Java/tools/build).
- Must not mutate repo state unless explicitly instructed by user within the session.

---

## Deterministic `.cfg` selection + co-location rule (TLC constraint)

### Why this exists
In this repo, TLC is invoked with:

- cwd = directory of the spec file
- `-config` set to **`path.basename(cfgFile)`**

(See `src/tools/tlc.ts`.)

Therefore the cfg file TLC uses must be **present in the same directory as the spec file** (or copied there first).

### Selection algorithm (must implement identically in `/tla-smoke`, `/tla-check`, `/tla-review`)

Inputs:
- `specPath = resolve($1 or stripLeadingAt($1))`
- `cfgArg = $2` if it ends with `.cfg` (otherwise treat `$2` as optional attachment)

Algorithm (two-phase; MUST follow in this order):

#### Phase 1: Ensure TLC tool precondition (`getSpecFiles`) will succeed

The MCP TLC tools in this repo call `getSpecFiles(specPath)` and **fail early** if it returns null.

`getSpecFiles` only recognizes:
- `<SpecName>.cfg` next to `<SpecName>.tla`, OR
- `MC<SpecName>.tla` + `MC<SpecName>.cfg`

Therefore, before calling any `tlaplus_mcp_tlc_*` tool, evaluate the precondition in this exact order:

1) If `<SpecName>.cfg` exists next to spec:
   - OK (precondition satisfied via `Spec.cfg`).
   - Note: if `MC<SpecName>.tla` + `MC<SpecName>.cfg` also exist, the MCP tool will still prefer `Spec.cfg` (because `getSpecFiles` checks `Spec.cfg` first). Document this in the command output when detected.

2) Else if `MC<SpecName>.tla` and `MC<SpecName>.cfg` both exist next to spec:
   - OK (precondition satisfied via MC pair).
   - IMPORTANT: Do **not** create `Spec.cfg` automatically in this case, because doing so would change the MCP tool’s default behavior away from the MC pair.

3) Else if `cfgArg` exists:
   - Copy `cfgArg` into the spec directory as `<SpecName>.cfg` (non-clobbering; if it somehow exists after re-check, skip copy)
   - This ensures `getSpecFiles` will succeed.

4) Else if `<SpecName>.generated.cfg` exists next to spec:
   - Copy it to `<SpecName>.cfg` (non-clobbering)

5) Else:
   - STOP and instruct the user to run `/tla-symbols <spec>` first (it will create `<SpecName>.cfg`).

#### Phase 2: Choose which cfg TLC should actually run with

After Phase 1, TLC can run. Now decide what to pass as `cfgFile`:

1) If `cfgArg` exists:
   - Resolve `cfgArg` to `cfgPath`.
   - If `dirname(cfgPath) == dirname(specPath)` (after realpath normalization): use `cfgPath`.
   - Else copy `cfgPath` into `dirname(specPath)` as:
     - `<SpecName>.override.cfg` if free
     - else `<SpecName>.override.1.cfg`, `.2`, ... (first available)
     - Then use the copied cfg.
2) Else:
   - Use the MCP tool’s default config:
     - If `<SpecName>.cfg` exists: use it
     - Else if `MC<SpecName>.cfg` exists and `MC<SpecName>.tla` exists: use `MC<SpecName>.cfg`
     - Else: (should be unreachable if Phase 1 was followed; treat as error)

**Required output**:
- Always print:
  - which branch satisfied Phase 1 ("Spec.cfg existed", "copied cfgArg to Spec.cfg", "copied Spec.generated.cfg to Spec.cfg", or "stopped")
  - which cfg was selected in Phase 2 ("explicit cfgArg", "Spec.cfg")

---

## Deterministic `.cfg` generation algorithm (`/tla-symbols`)

### Inputs
- `specPath`
- SANY symbol extraction result from `tlaplus_mcp_sany_symbol` with schema `SymbolExtractionResult`:
  - `candidates: { constants, variables, statePredicates, actionPredicates, temporalFormulas, ... }`
  - `bestGuess: { init, next, spec, invariants[], properties[] }`
  - Reference: `src/utils/symbols/types.ts:SymbolExtractionResult`

### Output file naming
- Primary: `<SpecName>.cfg` if absent
- Else: `<SpecName>.generated.cfg`

### Content rules (template; deterministic)
Write a cfg file that is syntactically valid and safe-by-default.

**Definition: “syntactically valid” (for generated `.cfg`)**
- The generated file must contain **no invalid, partially-specified directives**. In particular:
  - Do not emit `CONSTANT` / `CONSTANTS` keywords unless there is at least one concrete assignment on an uncommented line.
  - Do not emit `SPECIFICATION` / `INIT` / `NEXT` directives unless the chosen operator name is known.

This means the generated file can be syntactically valid but still require user edits before TLC will run; in that case, the file must include clear commented guidance.

1) Pick behavior spec (use **bestGuess**, never invent):
   - If `bestGuess.spec` is not null, write:
     - `SPECIFICATION <bestGuess.spec.name>`
   - Else if `bestGuess.init` and `bestGuess.next` are both not null, write:
     - `INIT <bestGuess.init.name>`
     - `NEXT <bestGuess.next.name>`
   - Else:
     - write commented placeholders:
       - `\* INIT <TODO>`
       - `\* NEXT <TODO>`
       - `\* SPECIFICATION <TODO>`
     - plus guidance: "Run /tla-parse and inspect operators; update cfg accordingly."

2) Invariants/properties (use **bestGuess.invariants/properties**, never invent):
   - For each `inv` in `bestGuess.invariants`, emit:
     - `INVARIANT <inv.name>`
   - For each `prop` in `bestGuess.properties`, emit:
     - `PROPERTY <prop.name>`
   - If both arrays are empty, emit commented guidance and no invariants/properties.

3) Constants (use **candidates.constants**, never invent values):
   - If `candidates.constants` is non-empty:
     - Emit **only commented stubs** (no uncommented `CONSTANT`/`CONSTANTS` header) using this exact template:

       ```
       \* Constants detected by SANY; TLC requires concrete assignments before model checking.
       \* Example: CONSTANT Max = 10
       \*
       \* CONSTANT <ConstName> = <TODO>
       ```

     - Repeat the last stub line once per constant.
   - If empty: omit constants section.

**Canonical example (constants present, unknown values)**:

```cfg
SPECIFICATION Spec

\* Constants detected by SANY; TLC requires concrete assignments before model checking.
\* Example: CONSTANT Max = 10
\*
\* CONSTANT Max = <TODO>
\* CONSTANT Min = <TODO>
```

4) Add a header comment block explaining:
   - how to run `/tla-check <spec> <cfg>`
   - that constants need assignments

### Validation step
- After writing, the command must advise the user to run `/tla-smoke <spec> <cfgWritten>` and fix constants if TLC complains.

---

## Canonical OpenCode Command Format (lock this down)

> OpenCode command name comes from the filename: `.opencode/commands/tla-parse.md` registers `/tla-parse`.

Use this structure for each command file:

```md
---
description: "Parse a TLA+ spec with SANY"
agent: build
---

## Usage

Preferred (always works):
  /tla-parse test-specs/Counter.tla

## What this does

1) Uses `$1` as the *filesystem path* for MCP tools.
2) Calls `tlaplus_mcp_sany_parse` with that path.

## Run

Use MCP tool `tlaplus_mcp_sany_parse` with:

- fileName: `$1`
```

**Why this format**:
- It avoids relying on uncertain `@file` argument preservation.
- It does not depend on `@...` expansion; the command can read the spec file for context.

**Frontmatter formatting rule (for our repo + lint tests)**:
- Use a standard frontmatter block:
  - opening `---` on its own line
  - one `key: value` per line
  - closing `---` on its own line
- Do not use condensed one-line YAML frontmatter.

## OpenCode Environment Assumptions (MUST be true)

These commands are prompts executed by an OpenCode agent. To make the deliverables feasible, we assume:

- The OpenCode agent used for these commands (recommended: `build`) has tools enabled:
  - **Read** (read `.tla` / `.cfg` inputs)
  - **Write/Edit** (needed for `/tla-symbols` to write `.cfg` files)
  - **Bash** (optional but useful for quick checks; not strictly required if the model uses filesystem tools)
  - **MCP access** (to call `tlaplus_mcp_*` tools)

**If the user’s OpenCode setup does not provide a `build` agent with these tools**:
- Commands should print an explicit error telling the user to run the command with an agent that has Write permissions (or to configure an agent accordingly), because `/tla-symbols` cannot meet its requirements otherwise.

---

## Deterministic File Operations Policy (copy/write must be implementable)

Because OpenCode commands are executed by an LLM with tools, we need an explicit, deterministic recipe for file operations.

### Preferred mechanism (cross-platform; no shell assumptions)

Use file tools only:

1) **Read** the source file contents.
2) **Write** the exact contents to the destination path.
3) Verify by **Read** that destination exists and has expected content length (>0).

### Fallback mechanism (optional)

If (and only if) Bash is available, the implementation may use platform-appropriate copy:
- Unix/macOS: `cp <src> <dst>`
- Windows (PowerShell): `Copy-Item <src> <dst>`

### Naming collision algorithm (deterministic)

When choosing a destination like `<SpecName>.override.cfg`:

1) Try `<SpecName>.override.cfg`.
2) If it exists, try `<SpecName>.override.1.cfg`, then `.2`, etc.
3) Use the first non-existing filename.


---

## Verification Strategy

### Test Decision
- **Infrastructure exists**: YES (Jest)
- **User wants tests**: YES (automated lint-style Jest tests for CI) + local E2E script (manual trigger)

### What CI Will Verify (Automated)
- Command files exist and parseable YAML frontmatter
- Required frontmatter keys present (at minimum `description` and `agent: build`)
- Templates contain required semantics:
  - mention MCP tool names (`tlaplus_mcp_*`)
  - mention stripping leading `@`
  - include at least one usage example
- Docs updated and no longer claim “commands not supported”

### What Local E2E Will Verify (Not CI)
- With OpenCode configured (model credentials), `opencode run --command <cmd> ...` succeeds and outputs deterministic markers from the command templates.

**E2E pass/fail signal (minimal but non-trivial)**:
- For each command invocation, require:
  - process exit code = 0, AND
  - stdout contains the deterministic markers our command templates require:
    - `Spec path:`
    - For TLC commands: `CFG used:`
    - For `/tla-symbols`: `CFG written:`
    - For `/tla-review`: `Review Summary`

---

## Execution Strategy

### Parallel Execution Waves

Wave 1 (start immediately)
├── Task 1: Validate OpenCode command semantics (filename→command name, `$ARGUMENTS`, `@file` behavior)
├── Task 2: Add `.opencode/commands/*.md` (initial versions)
└── Task 3: Add Jest lint tests scaffold

Wave 2 (after Wave 1)
├── Task 4: Update OPENCODE.md + README + INSTALLATION + TESTING
├── Task 5: Harden lint tests (cover edge cases, prevent regressions)
└── Task 6: Add local E2E runner script + docs

Critical Path: Task 1 → Task 2 → Task 4/5

---

## TODOs

### 1) Validate OpenCode command behavior (blocker check)

- [ ] Use the initial `.opencode/commands/tla-parse.md` as a “probe” (avoid creating throwaway files) to confirm:
  - Commands are auto-discovered from `.opencode/commands/*.md`
  - Command name derives from filename (e.g., `tla-parse.md` → `/tla-parse`)
  - `$ARGUMENTS` and `$1/$2` are substituted as expected
  - That `@path/to/file` as `$1` results in `$1` containing the literal token `@path/to/file` (so stripping `@` works). If not, document the limitation and require plain path as `$1`.

**Exact probe content requirements (no invention)**:
- Ensure `tla-parse.md` instructs the model to begin its response with a literal debug block like:
  
  ```
  [opencode-args]
  ARGUMENTS=$ARGUMENTS
  1=$1
  2=$2
  [/opencode-args]
  ```
  
  (The point is that the tester can see whether `$ARGUMENTS` contains a literal `@path` or not.)

**Exact invocations to test**:
1) Plain path only:
   - `/tla-parse test-specs/Counter.tla`
2) `@` only:
   - `/tla-parse @test-specs/Counter.tla`
3) Template-time `@` expansion (most important for usability):
   - Ensure the command body itself contains an `@` include that uses `$1` literally (e.g., a section like `Spec contents: @$1`).
   - Run (1) again and confirm whether OpenCode includes the spec contents when the template contains `@$1`.

**Record the results**:
- In `OPENCODE.md` (or `TESTING.md`), add a short note of what OpenCode did in case (2) so future contributors don’t re-discover this.

**Why this is critical**:
 MCP tools require a filesystem path (see `src/tools/sany.ts` and `src/tools/tlc.ts`). If OpenCode does not pass a usable token in `$1`, then the command must require plain paths.

**Fallback Decision (pre-approved)**:
- If `@file` in OpenCode does **not** preserve the literal `@path` argument, then:
  - Commands will require a **plain path** argument (first token) for MCP calls, and
  - Docs will not recommend passing `@path` as an argument for attachment; instead, commands will rely on explicit Read (and/or template-time `@$1` if confirmed in step (4)).

**Must NOT do**:
- Do not change MCP server code.

**References**:
- Official docs: https://opencode.ai/docs/commands/
- Official CLI docs: https://opencode.ai/docs/cli/

**Recommended Agent Profile**:
- **Category**: `quick`
  - Reason: small exploratory change + confirm observed behavior.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 1 (with Tasks 2 and 3)
- **Blocks**: Task 2 (exact template design)
- **Blocked By**: None

**Acceptance Criteria**:
- [x] In OpenCode TUI, the probe command runs and demonstrates how args are passed/substituted.
- [x] Document the observed behavior in the repo docs (OPENCODE.md or TESTING.md) and adjust command templates and lint tests accordingly.

### 2) Add OpenCode command files for all 6 `/tla-*`

- [x] Create directory `.opencode/commands/` (if missing).
- [x] Add the following markdown command files:
  - `.opencode/commands/tla-parse.md`
  - `.opencode/commands/tla-symbols.md`
  - `.opencode/commands/tla-smoke.md`
  - `.opencode/commands/tla-check.md`
  - `.opencode/commands/tla-review.md`
  - `.opencode/commands/tla-setup.md`

**Command content requirements** (each):
- Uses OpenCode command frontmatter (at least `description:`). Prefer setting `agent: build` to ensure tool availability.
- Accepts spec path as plain path (`$1`).
  - Best-effort convenience: if `$1` starts with `@`, strip leading `@` and proceed only if it resolves to an existing `.tla` file on disk.
  - Do not depend on runtime `@file` expansion or treat `@path` as a standardized second argument.
- Calls correct MCP tools:
  - parse → `tlaplus_mcp_sany_parse`
  - symbols → `tlaplus_mcp_sany_symbol` (+ generate/write `.cfg`)
  - smoke → `tlaplus_mcp_tlc_smoke`
  - check → `tlaplus_mcp_tlc_check`
  - review → parse + symbols + smoke + checklist
  - setup → validates Java/tools build prerequisites (guided)

**Specific behavioral requirements**:
- `/tla-symbols`:
  - Writes a `.cfg` file next to the `.tla` file (naming convention: `Spec.tla` → `Spec.cfg`).
  - Must not silently overwrite an existing `.cfg`.
    - **Default behavior**: If `Spec.cfg` already exists, write `Spec.generated.cfg` instead.
    - **Integration requirement**: downstream TLC commands (`/tla-smoke`, `/tla-check`, `/tla-review`) must follow the canonical “two-phase” `.cfg` algorithm in this plan to satisfy:
      1) the MCP TLC tool precondition (`getSpecFiles` requires `Spec.cfg` or `MCSpec.*`), and
      2) the TLC `-config` basename constraint (cfg must be co-located with spec).
- `/tla-review`:
  - Runs smoke test by default.
  - If no `.cfg` exists, should suggest running `/tla-symbols` first (or generate one).

**Deterministic `.cfg` handling (single source of truth)**:
- Do **not** implement ad-hoc selection logic in individual command templates.
- Instead, implement exactly the section:
  - **“Deterministic `.cfg` selection + co-location rule (TLC constraint)”**
  - (including Phase 1: create/copy `Spec.cfg` to satisfy `getSpecFiles`, and Phase 2: optional override cfg selection + co-location copy).

**Command output markers (required for local E2E + helpful for users)**:
- `/tla-parse`: must print `Spec path:`
- `/tla-symbols`: must print `Spec path:` and `CFG written:`
- `/tla-smoke`: must print `Spec path:` and `CFG used:`
- `/tla-check`: must print `Spec path:` and `CFG used:`
- `/tla-review`: must print `Review Summary` plus `Spec path:` and (if smoke runs) `CFG used:`
- `/tla-setup`: must print `Setup Summary`

**Windows/paths guardrail**:
- Commands must not assume POSIX separators; instructions/examples should work with relative paths from repo root.
- If quoting is needed for spaces, docs should show quoting patterns that OpenCode accepts.

**Recommended Agent Profile**:
- **Category**: `writing`
  - Reason: primarily authoring markdown command templates and usage guidance.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 1 (with Task 3; after Task 1 reveals any template constraints)
- **Blocks**: Task 4 (docs should point to these files) and Task 6 (E2E runner references command names)
- **Blocked By**: Task 1 findings

**References**:
- Existing Claude Code commands (behavioral guidance): `commands/tla-parse.md`, `commands/tla-symbols.md`, `commands/tla-smoke.md`, `commands/tla-check.md`, `commands/tla-review.md`, `commands/tla-setup.md`
- MCP tool file path resolution and existence requirements:
  - `src/tools/sany.ts` (path resolving + error messaging)
  - `src/tools/tlc.ts` (cfg detection; smoke default 3s; **passes cfg basename only**)
- TLC cfg auto-detection rules (to avoid wrong assumptions):
  - `src/utils/tlc-helpers.ts:getSpecFiles()`
    - auto-detects only `Spec.cfg` next to `Spec.tla`, or `MCSpec.tla` + `MCSpec.cfg` pair
- MCP server registration context: `src/server.ts`
- Example specs/configs for examples and validation:
  - `test-specs/Counter.tla`, `test-specs/Counter.cfg`

**Acceptance Criteria**:
- [ ] All 6 files exist under `.opencode/commands/`.
- [ ] In OpenCode TUI, each command appears and can be invoked.
- [ ] Each command template includes at least one example call using a plain path.
- [ ] Each command template documents the best-effort convenience that a user-typed leading `@` in `$1` will be stripped (strip-and-validate), but does not depend on runtime `@file` expansion.

### 3) Add Jest lint tests for OpenCode commands (CI-safe automation)

- [x] Add Jest tests that:
  - Glob `.opencode/commands/*.md`
  - Parse YAML frontmatter and assert required keys exist
  - Assert the body includes:
    - the relevant `tlaplus_mcp_*` tool names
    - a clear instruction to strip leading `@`
    - at least one usage example
- [ ] Add tests that assert docs no longer claim OpenCode “Commands not supported”.

**Critical placement requirement (Jest roots)**:
- Jest is configured with `roots: ['<rootDir>/src']` (see `jest.config.js`). Therefore, the new tests MUST live under `src/` (e.g., `src/__tests__/opencode-commands-lint.test.ts`) or they will not run in CI.

**Notes**:
- Prefer no new dependencies.
- Parsing approach (DECIDED): Implement a **minimal frontmatter key-value parser inside the Jest test** that:
  - reads between the first two `---` lines
  - supports `key: value` single-line pairs for keys we care about (`description`, `agent`, `model`, `subtask`)
  - does not attempt full YAML (we only lint our own command files)

**Lint rules (DECIDED; deterministic)**:
- For each `.opencode/commands/*.md`:
  - must have frontmatter
  - must contain `description:`
  - must contain `agent: build` (required)
  - must include the specific MCP tool(s) expected for that command name
  - must include a "Preferred" usage example with plain path
  - must include a short note about `@` handling: "If you typed `@path.tla` as the first argument, this command strips the leading `@` and validates the file exists."

**Post-probe consistency rule**:
- If Task 1 concludes that OpenCode does not preserve a usable token in `$1` when the user types `@path` as the first argument, the command templates must:
  - stop supporting `@path` as `$1` (document plain-path-only), and
  - rely exclusively on explicit file Read (and/or template-time `@$1` if confirmed) for spec contents.

**Actionable failure messages (examples)**:
- `tla-check.md missing required MCP tool reference: tlaplus_mcp_tlc_check`
- `tla-parse.md missing usage example: /tla-parse test-specs/Counter.tla`

**Recommended Agent Profile**:
- **Category**: `quick`
  - Reason: adding a small, focused Jest test suite.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 1 (with Task 2)
- **Blocks**: Task 5 (hardening)
- **Blocked By**: None

**References**:
- Jest config: `jest.config.js`
- Existing Jest patterns: `src/tools/__tests__/sany.test.ts`, `src/tools/__tests__/tlc.test.ts`
- CI executes: `npm test` via `.github/workflows/ci.yml`

**Acceptance Criteria**:
- [ ] `npm test` passes locally.
- [ ] CI passes on ubuntu/macos/windows.

### 4) Update docs to reflect OpenCode command support

- [ ] Update `OPENCODE.md`:
  - Replace the “Commands not supported” section with accurate info.
  - Document that repo ships `.opencode/commands/tla-*.md` and how to use them.
  - Add a note about `@path` vs plain path and “strip leading `@`” semantics.
- [ ] Update `README.md`:
  - Clarify `/tla-*` availability for OpenCode (via `.opencode/commands`) vs Claude Code (plugin commands).
- [ ] Update `INSTALLATION.md`:
  - Ensure OpenCode install/run instructions match `.opencode/opencode.json` auto-detection.
- [ ] Update `TESTING.md`:
  - Add/replace a section describing automated Jest lint tests for OpenCode commands.
  - Add instructions for local E2E script (prereqs, what it validates).

**Must NOT do**:
- Do not remove Claude Code instructions; instead, clarify platform differences.

**Acceptance Criteria**:
- [ ] Docs contain no contradictions about OpenCode command support.
- [ ] Docs provide at least one OpenCode example for each command.

**Concrete doc claims that MUST be removed/changed**:
- In `OPENCODE.md`, remove/replace:
  - the support matrix row that says `Commands | ❌ Not Supported`
  - the later repeated section "Known Limitations → Commands Not Supported" listing `/tla-*` as unavailable
- In `README.md`, ensure any `/tla-*` mention is explicitly attributed:
  - Claude Code: plugin slash-commands, OR
  - OpenCode: `.opencode/commands` shipped by this repo
- In `INSTALLATION.md`, ensure OpenCode steps match `.opencode/opencode.json` auto-detection (and not Claude plugin installation).
- In `TESTING.md`, add a dedicated OpenCode section describing:
  - CI lint tests (what they check)
  - local E2E script (how to run, prerequisites)

**Recommended Agent Profile**:
- **Category**: `writing`
  - Reason: multi-file documentation corrections and clarity improvements.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 2 (with Task 5)
- **Blocks**: none
- **Blocked By**: Task 2 (commands exist) and Task 3 (lint expectations)

### 5) Harden Jest lint tests (regression prevention)

- [ ] Add edge-case checks:
  - Ensure filenames match command names (`tla-parse.md` etc.)
  - Ensure all 6 expected commands exist (not just “some”).
  - Ensure OPENCODE.md no longer contains the old support table entries claiming commands are unsupported.

**Acceptance Criteria**:
- [ ] Lint tests fail with actionable messages if a command is missing/malformed.

**Recommended Agent Profile**:
- **Category**: `quick`
  - Reason: incremental test improvements.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 2 (with Task 4)
- **Blocks**: none
- **Blocked By**: Task 3

### 6) Add local-only E2E runner script for OpenCode commands

- [ ] Add a local E2E runner script (Node-based; cross-platform):
  - File: `scripts/opencode-e2e.mjs`
  - NPM script: `opencode:e2e` → `node scripts/opencode-e2e.mjs`
  - Requires OpenCode CLI in PATH.
  - Implements deterministic enable/skip rule:
    - If `OPENCODE_E2E` env var is not `1`, print `SKIP: OPENCODE_E2E not set` and exit 0.
    - If `OPENCODE_E2E=1`, execute suite and exit non-zero if any command fails.
  - Preflight checks (when `OPENCODE_E2E=1`):
    - `opencode --version` runs
    - `opencode run --help` output contains `--command`
  - Runs the following suite (all commands):
    1) `opencode run --command tla-parse test-specs/Counter.tla`
    2) `opencode run --command tla-symbols test-specs/Counter.tla`
    3) `opencode run --command tla-smoke test-specs/Counter.tla`
    4) `opencode run --command tla-check test-specs/Counter.tla test-specs/Counter.cfg`
    5) `opencode run --command tla-review test-specs/Counter.tla`
    6) `opencode run --command tla-setup`
  - For each invocation, asserts stdout contains the deterministic markers required by this plan:
    - `Spec path:`
    - For TLC commands: `CFG used:`
    - For `/tla-symbols`: `CFG written:`
    - For `/tla-review`: `Review Summary`
  - If failures indicate missing OpenCode model/provider configuration, print a clear diagnostic and exit non-zero (since `OPENCODE_E2E=1` implies user asked for strict mode).

- [ ] Update `TESTING.md` with a short "OpenCode E2E" section:
  - prerequisites
  - how to run: `OPENCODE_E2E=1 npm run opencode:e2e`
  - what it validates (marker-based contract)

**Guardrail**:
- Do not run E2E in CI; keep it local-only.

**Explicit expectation**:
- The local E2E is "best effort" and may require a configured model provider + OpenCode setup.
- Deterministic enable/skip rule (DECIDED):
  - If `OPENCODE_E2E` env var is not set to `1`, the script **prints SKIP** and exits 0.
  - If `OPENCODE_E2E=1`, the script runs the E2E suite and exits non-zero on any command failure.

**References**:
- OpenCode CLI help (local): `opencode run --help` shows `--command` exists
- Example specs: `test-specs/Counter.tla`, `test-specs/Counter.cfg`

**Acceptance Criteria**:
- [ ] Script exists and is documented in `TESTING.md`.
- [ ] Script can be run locally by developers (given OpenCode configured).

**Recommended Agent Profile**:
- **Category**: `unspecified-low`
  - Reason: small Node script + docs; needs careful cross-platform handling.
- **Skills**: (none required)

**Parallelization**:
- **Can Run In Parallel**: YES
- **Parallel Group**: Wave 2 (after Task 2)
- **Blocks**: none
- **Blocked By**: Task 2

---

## Commit Strategy (suggested)

1. `docs(opencode): correct command support claims` (OPENCODE.md/README/INSTALLATION/TESTING)
2. `feat(opencode): add .opencode/commands tla-*` (6 command files)
3. `test(opencode): add Jest lint tests for commands/docs` (CI-safe automation)
4. `chore(opencode): add local e2e runner for commands` (scripts + docs)

---

## Success Criteria

### CI Verification
- [ ] `npm run build` passes
- [ ] `npm test` passes (including new command/doc lint tests)

### Manual Spot Check (developer workstation)
- [ ] Start `opencode` in repo root (auto-detect `.opencode/opencode.json`)
- [ ] Run `/tla-parse test-specs/Counter.tla` and confirm it triggers `tlaplus_mcp_sany_parse` using path `test-specs/Counter.tla`
- [ ] Run `/tla-review test-specs/Counter.tla` and confirm smoke is executed by default
