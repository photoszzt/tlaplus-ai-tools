---
name: tla-review
description: Comprehensive TLA+ specification review with checklist and automated validation
argument-hint: "@spec.tla"
allowed-tools: [Read, Bash, Grep, Task]
---

# Comprehensive Spec Review

Perform a thorough review of TLA+ specifications using systematic checklist and automated validation with the spec-validator agent.

## Usage

```
/tla-review @Counter.tla
/tla-review @System.tla
```

## What This Command Does

1. Loads the tla-spec-review skill
2. Walks through review checklist interactively
3. Runs automated validation with spec-validator agent
4. Checks syntax with SANY parse
5. Runs smoke test for quick validation
6. Generates comprehensive review report
7. Provides specific recommendations

## Review Process

### Phase 1: Structure Review (Interactive)

#### Module Declaration
- ✓ Module name matches filename?
- ✓ EXTENDS necessary and sufficient?
- ✓ INSTANCE used correctly?

#### Constants and Variables
- ✓ All constants declared?
- ✓ ASSUME statements validate constraints?
- ✓ All variables declared?
- ✓ Names clear and descriptive?

#### Init Predicate
- ✓ Initializes ALL variables?
- ✓ No primed variables?
- ✓ Well-defined initial state?

#### Next Action
- ✓ Covers all transitions?
- ✓ Uses disjunction for multiple actions?
- ✓ Primed variables correct?

#### Specification Formula
- ✓ Follows `Init /\ [][Next]_vars` pattern?
- ✓ Fairness appropriate?
- ✓ Stuttering allowed where needed?

#### Invariants and Properties
- ✓ Type invariants defined?
- ✓ Safety properties clear?
- ✓ Liveness properties correct?
- ✓ Temporal formulas accurate?

### Phase 2: Automated Validation

Spawns spec-validator agent to:
- Parse with SANY (detect syntax errors)
- Run smoke test (find quick bugs)
- Check common pitfalls (EXCEPT syntax, primed variables)
- Analyze naming conventions
- Verify completeness

### Phase 3: Report Generation

Creates review report with:
- ✅ Passed checks
- ⚠️ Warnings (non-critical issues)
- ❌ Errors (must fix)
- 💡 Recommendations (improvements)

## Sample Output

```
=== TLA+ Specification Review: Counter.tla ===

Phase 1: Structure Review
━━━━━━━━━━━━━━━━━━━━━━━━━━
Module Declaration
  ✓ Module name matches filename
  ✓ EXTENDS Naturals (appropriate)

Constants & Variables
  ✓ CONSTANT MaxValue declared
  ✓ ASSUME validates MaxValue
  ✓ VARIABLE count declared
  ✓ Names are clear

Init Predicate
  ✓ Initializes all variables
  ✓ No primed variables
  ✓ Well-defined

Next Action
  ✓ All actions covered
  ✓ Primed variables correct
  ⚠️ Consider adding UNCHANGED when needed

Phase 2: Automated Validation
━━━━━━━━━━━━━━━━━━━━━━━━━━
Running spec-validator agent...

Parse Check
  ✓ No syntax errors

Smoke Test (3s)
  ✓ No invariant violations found
  ✓ Generated 847 states

Common Pitfalls
  ✓ No EXCEPT syntax errors
  ✓ No primed variables in invariants
  ✓ UNCHANGED used appropriately

Phase 3: Summary
━━━━━━━━━━━━━━━━━━━━━━━━━━
Checks Passed: 15/16
Warnings: 1
Errors: 0

⚠️ Warning: Consider using UNCHANGED explicitly
   Line 14: count' = count + 1
   Consider: count' = count + 1 /\ UNCHANGED <<>>

💡 Recommendations:
   1. Add more invariants to catch edge cases
   2. Consider temporal properties for liveness
   3. Test with larger MaxValue (currently 10)

Overall: GOOD - Spec is well-structured
         Ready for model checking with /tla-check
```

## When to Use

### Before Model Checking
Pre-check before running expensive model check:
```
1. /tla-review @Spec.tla
2. Fix issues
3. /tla-check @Spec.tla
```

### Code Review
Review specs before merging:
```
1. Team member writes spec
2. Reviewer runs /tla-review
3. Discuss findings
4. Approve or request changes
```

### Learning TLA+
Understand best practices:
```
/tla-review @MyFirstSpec.tla
```
Learn what to improve.

### Spec Refactoring
Validate after major changes:
```
1. Refactor spec
2. /tla-review @Spec.tla
3. Ensure still follows best practices
```

## Review Depth

### Quick Review (Default)
- Structure checklist
- Parse and smoke test
- Common pitfalls
- ~2-3 minutes

### Deep Review
Ask for deeper analysis:
```
/tla-review @Spec.tla --deep
```
- Full checklist with explanations
- Extended smoke test (10s)
- Style and naming analysis
- Performance recommendations
- ~5-10 minutes

## Common Issues Found

### Structural Issues
- Missing variable initialization in Init
- Primed variables in invariants
- Incomplete Next action (missing cases)
- No type invariants

### Syntax Issues
- EXCEPT syntax errors: `[f EXCEPT [x] = y]` → `[f EXCEPT ![x] = y]`
- Wrong operator precedence
- Undefined symbols

### Logic Issues
- Invariants too weak (don't catch bugs)
- Missing fairness conditions
- Incorrect temporal formulas
- Stuttering not allowed when needed

### Style Issues
- Unclear naming
- Missing comments
- Inconsistent formatting
- Complex nested expressions

## Fixing Issues

After review, fix issues in this order:

1. **Errors** (must fix) - Prevent model checking
   ```
   ❌ Syntax error at line 15
   → Fix immediately
   ```

2. **Warnings** (should fix) - May cause problems
   ```
   ⚠️ Missing UNCHANGED
   → Add for clarity
   ```

3. **Recommendations** (good practice) - Improvements
   ```
   💡 Add more invariants
   → Consider for robustness
   ```

## Tips

### Use Early and Often
Review during development, not just at end:
```
Write Init → Review
Write Next → Review
Write Invariants → Review
```

### Iterative Improvement
Each review cycle:
```
1. /tla-review
2. Fix top issue
3. Repeat until clean
```

### Learn from Reviews
Pay attention to recommendations:
- Understand why issues flagged
- Learn TLA+ best practices
- Improve future specs

### Combine with Other Commands
Complete workflow:
```
1. /tla-parse   (syntax check)
2. /tla-review  (structure review)
3. /tla-smoke   (quick test)
4. /tla-check   (full verification)
```

## Customization

Create project-specific review standards:
1. Define team conventions
2. Add to `.claude/tlaplus.local.md`
3. Review command uses custom standards

## Related Commands

- `/tla-parse` - Quick syntax check
- `/tla-smoke` - Fast validation
- `/tla-check` - Full model checking
- `/tla-symbols` - Analyze spec structure

## Related Skills

- `tla-spec-review` - Detailed review guidelines
- `tla-debug-violations` - Debug found issues
- `tla-getting-started` - Learn TLA+ basics

## Related Agents

- **spec-validator** - Automated validation
  (Spawned automatically by this command)

## Implementation

1. Load tla-spec-review skill into context
2. Present interactive checklist to user
3. Spawn spec-validator agent with Task tool:
   ```javascript
   Task({
     subagent_type: "spec-validator",
     prompt: `Validate specification at ${filePath}`,
     description: "Validating TLA+ spec"
   })
   ```
4. Collect checklist responses
5. Combine with agent results
6. Generate formatted report
7. Provide actionable recommendations

Present results in clear, structured format with color coding and priority levels.
