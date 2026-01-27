# TLA+ Debugging Strategies

Advanced strategies for debugging TLA+ specification violations.

## General Debugging Approach

### 1. Reproduce the Issue

Make violation consistent:
- Use same constants
- Same configuration
- Same TLC seed (if random)
- Document exact steps

### 2. Minimize the Counterexample

Reduce to smallest failing case:
- Decrease constants
- Simplify configuration
- Remove non-essential properties
- Find minimal reproduction

### 3. Understand the Trace

Analyze execution:
- Read trace carefully
- Understand each state
- Identify transitions
- Find unexpected changes

### 4. Form Hypothesis

Guess what's wrong:
- Which action is buggy?
- Is guard too weak?
- Is initialization wrong?
- Is invariant too strong?

### 5. Test Hypothesis

Verify your guess:
- Add temporary invariants
- Add Print statements
- Modify spec slightly
- Re-run model checking

### 6. Fix and Verify

Apply fix:
- Make minimal change
- Re-run all checks
- Test with larger constants
- Document the fix

## Invariant Violation Debugging

### Understand the Invariant

What does it check?
```tla
BoundInvariant == count <= MaxValue
```
Checks: count never exceeds MaxValue

### Find Violation State

In trace, which state violates?
```
State 1: count = 0    ✓
State 2: count = 5    ✓
State 3: count = 11   ✗ Violation!
```

### Identify Transition

Which action caused it?
```
State 2 → State 3: Action Increment
```

### Analyze Action

Is action buggy?
```tla
Increment ==
    /\ count' = count + 10    \* BUG: No guard!
```

Fix: Add guard
```tla
Increment ==
    /\ count + 10 <= MaxValue  \* Add guard
    /\ count' = count + 10
```

## Property Violation Debugging

### Liveness Violations

**Symptom**: Property `<>P` or `[]<>P` fails

**Common causes**:
1. Missing fairness (WF or SF)
2. Deadlock
3. Incorrect formula

**Debug steps**:
1. Check if deadlock:
   ```tla
   NoDeadlock == ENABLED <<Next>>_vars
   INVARIANT NoDeadlock
   ```

2. Add fairness:
   ```tla
   Spec == Init /\ [][Next]_vars /\ WF_vars(Action)
   ```

3. Verify formula matches intent

### Stuttering Issues

**Symptom**: Property fails due to stuttering

**Solution**: Check specification formula
```tla
\* Wrong (doesn't allow stuttering)
Spec == Init /\ <<Next>>_vars

\* Right (allows stuttering)
Spec == Init /\ [][Next]_vars
```

### Fairness Issues

**Strong vs Weak**:
- **WF_vars(A)**: If A stays enabled, eventually happens
- **SF_vars(A)**: If A infinitely often enabled, eventually happens

Choose based on system guarantees.

## Common Bug Patterns

### Off-by-One Errors

```tla
\* Bug
Action == count < Max /\ count' = count + 1  \* Allows count = Max

\* Fix
Action == count < Max - 1 /\ count' = count + 1
\* Or
Action == count + 1 < Max /\ count' = count + 1
```

### Missing Guards

```tla
\* Bug - always fires
Remove(item) ==
    /\ items' = items \ {item}

\* Fix - check item exists
Remove(item) ==
    /\ item \in items           \* Add guard
    /\ items' = items \ {item}
```

### Uninitialized Variables

```tla
\* Bug - forgot to initialize y
Init == x = 0

\* Fix - initialize all variables
Init == x = 0 /\ y = 0
```

### Wrong EXCEPT Syntax

```tla
\* Bug - missing !
f' = [f EXCEPT [key] = value]

\* Fix - add !
f' = [f EXCEPT ![key] = value]
```

### Missing UNCHANGED

```tla
\* Bug - what happens to y?
Action == x' = x + 1

\* Fix - explicit UNCHANGED
Action == x' = x + 1 /\ UNCHANGED y
```

## Advanced Debugging Techniques

### Add Intermediate Invariants

Catch bugs earlier:
```tla
\* Original invariant
FinalInvariant == result = ExpectedResult

\* Add intermediate checks
Step1Done => Step1Correct
Step2Done => Step2Correct
...

\* Narrows down where bug occurs
```

### Use TLC's Print

Add visibility:
```tla
Action ==
    /\ condition
    /\ x' = Print("x is now", newValue)
    /\ ...
```

Prints during model checking.

### Constrain State Space

Focus on problematic area:
```tla
CONSTRAINT
    suspiciousVar <= 10  \* Limit to where bug occurs
```

### Binary Search on Constants

Find threshold where bug appears:
```
N = 5:  Pass
N = 10: Fail
N = 7:  Pass
N = 8:  Fail  <- Bug threshold found
```

### Simplify Spec Temporarily

Comment out parts:
```tla
Next ==
    \/ Action1
    \/ Action2
    (* \/ Action3  \* Comment out to test *)
```

Find which action causes issue.

## Trace Analysis Techniques

### State Diffing

Compare successive states:
```
State 1: x = 5, y = 0, status = "idle"
State 2: x = 5, y = 1, status = "active"

Changed: y (0 → 1), status ("idle" → "active")
Action: StartProcessing (based on changes)
```

### Identify Unexpected Changes

```
Expected: x increments by 1
Actual:   x jumped from 5 to 15

Why? Check action logic for bug.
```

### Trace Patterns

Look for repeated patterns:
```
State 1-5:   Normal progression
State 6-10:  Stuck in loop
State 11:    Violation

Issue likely in loop logic (states 6-10).
```

## Configuration Debugging

### Separate Concerns

Debug one thing at a time:
```
\* First: Check only type invariant
INVARIANT TypeInvariant

\* After passing: Add safety
INVARIANT TypeInvariant
INVARIANT SafetyProperty

\* After passing: Add liveness
PROPERTY LivenessProperty
```

### Use Different Constants

```
Small.cfg:    N = 2  (quick testing)
Medium.cfg:   N = 5  (thorough testing)
Large.cfg:    N = 10 (stress testing)
```

### Add Constraints

Limit to problematic region:
```
CONSTRAINT
    depth <= 20       \* Limit trace length
    count <= 100      \* Focus on small values
```

## When Stuck

### Take a Break

Fresh perspective helps.

### Ask for Help

- Review trace with colleague
- Post on TLA+ forum
- Use trace-analyzer agent

### Simplify Problem

Start from working spec:
```
1. Take last working version
2. Add changes incrementally
3. Test after each change
4. Identify breaking change
```

### Check Assumptions

Question everything:
```
- Is invariant correct?
- Is spec modeling right thing?
- Are constants reasonable?
- Is configuration valid?
```

## Prevention

### Write Tests Incrementally

```
1. Write Init
2. Test Init (check type invariant)
3. Add one action
4. Test action
5. Repeat
```

### Use Strong Type Invariants

Catch bugs early:
```tla
TypeInvariant ==
    /\ count \in Nat
    /\ status \in {"idle", "active", "done"}
    /\ messages \in Seq(MessageType)
    /\ clients \subseteq Clients
```

### Review Before Checking

Use `/tla-review` before model checking.

### Start with Small Constants

Find bugs in small state spaces first.

## Documentation

### Record Bugs Found

Document:
- What was wrong
- How to reproduce
- What fixed it
- Lesson learned

### Add Comments

```tla
\* FIXED: Previously missing guard caused overflow
\* See bug report #123
Action ==
    /\ count + 1 <= Max  \* Essential guard
    /\ count' = count + 1
```

## Summary

Systematic debugging:
1. Reproduce consistently
2. Minimize counterexample
3. Understand trace thoroughly
4. Form hypothesis
5. Test hypothesis
6. Fix and verify
7. Document learnings

Most bugs are:
- Missing guards
- Wrong initialization
- Incorrect EXCEPT syntax
- Missing UNCHANGED
- Off-by-one errors

Use tools and agents:
- `/tla-parse` - Syntax check
- `/tla-smoke` - Quick test
- trace-analyzer agent - Analyze violations
- `/tla-review` - Review structure

Debugging TLA+ specifications is an iterative process - each bug fixed teaches you more about the system and makes future bugs easier to find.
