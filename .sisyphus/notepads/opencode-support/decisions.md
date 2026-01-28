
## Skills Copy Decision (2026-01-28)

### Context
Task 4 tested all 6 TLA+ skills to determine which are accessible in OpenCode.

### Test Results
- **Accessible (3)**: tla-spec-review, tla-debug-violations, tla-create-animations
- **Missing (3)**: tla-getting-started, tla-model-checking, tla-refinement-proofs

### Root Cause
OpenCode discovers skills from `.claude/skills/` directory, not from `skills/` directory specified in `.claude-plugin/plugin.json` (Claude Code-specific).

### DECISION
**Copy 3 missing skills from `skills/` to `.claude/skills/`**

Skills to copy:
1. `skills/tla-getting-started/` → `.claude/skills/tla-getting-started/`
2. `skills/tla-model-checking/` → `.claude/skills/tla-model-checking/`
3. `skills/tla-refinement-proofs/` → `.claude/skills/tla-refinement-proofs/`

### Rationale
- OpenCode only discovers skills from `.claude/skills/` directory
- All 6 skills need to be accessible for complete TLA+ support
- Copying maintains compatibility with both Claude Code and OpenCode
- No changes needed to existing 3 skills (already in `.claude/skills/`)

### Next Step
Task 5 will execute the copy operation.
