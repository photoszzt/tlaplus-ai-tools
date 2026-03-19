# Checking Refinement

This reference covers techniques for verifying refinement with TLC, including invariant checking, trace analysis, and diagnosing common failures.

## Invariant Checking

Abstract invariants should hold on concrete specifications:

```
\* In concrete config — use the refinement mapping operator names directly
INVARIANT TypeInvariant
INVARIANT SafetyProperty
```

## Trace Checking

If refinement fails:

1. TLC shows counterexample
2. Trace shows concrete behavior
3. Find where abstract property violated
4. Fix concrete spec or refinement mapping

## Common Failures

### Wrong Mapping

```
count == x * y  \* Should be x + y
```

Fix: Correct the mapping function.

### Missing Initialization

```
\* Abstract: x = 0
\* Concrete: forgot to set something
```

Fix: Initialize all concrete state.

### Extra Behaviors

```
\* Concrete allows actions abstract doesn't
```

Fix: Strengthen concrete guards or abstract spec.

## TLC-Based vs TLAPS Proofs

### TLC (Model Checking)

**Pros**:

- Automatic verification
- Finds counterexamples
- Easy to use

**Cons**:

- Finite state spaces only
- Not a mathematical proof
- Bounded checking

**When to use**: Most practical refinement checking.

### TLAPS (Proof System)

**Pros**:

- Mathematical proofs
- Works for infinite state spaces
- Complete verification

**Cons**:

- Requires manual proof
- Steeper learning curve
- More time-consuming

**When to use**: Critical systems, academic research, when TLC insufficient.

## TLAPS Overview

For formal proofs (advanced topic):

```tla
THEOREM RefinementTheorem ==
    ASSUME AbstractSpec, ConcreteSpec, Mapping
    PROVE ConcreteSpec => AbstractSpec
PROOF
    <1>1. Init => AbstractInit BY Mapping
    <1>2. [Next]_vars => [AbstractNext]_abstractVars BY Mapping
    <1>3. QED BY <1>1, <1>2
```

See `tlaps-guide.md` for full TLAPS details.
