# Checking Refinement

This reference covers techniques for verifying refinement with TLC, including invariant checking, trace analysis, and diagnosing common failures.

## Invariant Checking

Abstract invariants should hold on concrete specifications:

In the concrete spec's config file, use the refinement mapping operator names directly:

```
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

```tla
\* Bug: wrong mapping expression
A == INSTANCE AbstractCounter WITH count <- x * y

\* Fix: correct the arithmetic
A == INSTANCE AbstractCounter WITH count <- x + y
```

### Missing Initialization

```tla
\* Bug: concrete Init doesn't establish abstract Init
Init == x = 0
\* Missing: y is uninitialized, but abstract expects count = x + y = 0

\* Fix: initialize all variables so mapping satisfies abstract Init
Init == x = 0 /\ y = 0
```

### Extra Behaviors

```tla
\* Bug: concrete allows decrement, but abstract only allows increment
Decrement == x > 0 /\ x' = x - 1 /\ UNCHANGED y

\* Fix: remove the action, or add it to abstract spec too
\* If concrete has behaviors abstract doesn't, refinement fails
```

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

For formal refinement proofs using the TLA+ Proof System (TLAPS), see `tlaps-guide.md` for the complete guide covering proof structure, tactics, and worked examples.
