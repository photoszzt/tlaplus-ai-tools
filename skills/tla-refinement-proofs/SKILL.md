---
name: tla-refinement-proofs
description: >-
  This skill provides guidance on specification refinement — proving that one TLA+ specification correctly implements another.
  It should be used when the user asks about "refinement", "specification refinement", "refine specification",
  "abstract and concrete specs", "implementation correctness", "prove implementation correct",
  "specification layers", "refinement mapping", "INSTANCE WITH", "TLAPS", "stuttering steps", "data refinement",
  or mentions proving one spec implements another.
version: 1.0.0
---

# TLA+ Refinement and Specification Relationships

This skill provides guidance on specification refinement - proving that one specification correctly implements another.

## When to Use

- Showing implementation refines abstract specification
- Verifying concrete spec satisfies abstract properties
- Relating high-level and low-level specifications
- Proving correctness of optimizations
- Understanding refinement mappings

## What is Refinement?

**Refinement** proves that a concrete (implementation) specification correctly implements an abstract (high-level) specification. Every behavior allowed by the concrete spec must correspond to a behavior allowed by the abstract spec.

**Why Refine?** Layered design, verified implementation, optimization verification, and interface compliance.

## Types of Refinement

**Safety Refinement**: Concrete spec's behaviors are a subset of abstract spec's behaviors. Define a refinement mapping, then check with TLC.

**Liveness Refinement**: Concrete spec satisfies abstract spec's liveness properties. Requires safety refinement plus fairness conditions.

## Refinement Workflow with TLC

### 1. Create Abstract Specification

```tla
---- MODULE AbstractCounter ----
EXTENDS Naturals
VARIABLE count
Init == count = 0
Inc == count' = count + 1
Spec == Init /\ [][Inc]_count
====
```

### 2. Create Concrete Specification

```tla
---- MODULE ConcreteCounter ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
IncX == x' = x + 1 /\ UNCHANGED y
IncY == y' = y + 1 /\ UNCHANGED x
Spec == Init /\ [][IncX \/ IncY]_<<x,y>>
====
```

### 3. Define Refinement Mapping and Check

In concrete spec, instantiate abstract with mapping:

```tla
A == INSTANCE AbstractCounter WITH count <- x + y
THEOREM Spec => A!Spec
```

### 4. TLC Configuration

```
SPECIFICATION Spec
PROPERTY A!Spec
```

### 5. Run TLC

```
/tla-check @QueueRefinement.tla    \* or the path to your refinement spec, e.g., @examples/QueueRefinement.tla
```

If passes: concrete refines abstract. If fails: trace shows where refinement breaks.

## Quick Reference

```tla
---- MODULE Concrete ----
VARIABLES ...concrete vars...
ConcreteSpec == ConcreteInit /\ [][ConcreteNext]_vars

A == INSTANCE Abstract WITH abstractVar <- mappingExpression

THEOREM ConcreteSpec => A!Spec
====
```

## Best Practices

1. Verify concrete spec correct on its own first
2. Check type refinement, then safety, then liveness
3. Comment refinement mappings clearly
4. Chain refinements for complex systems (Spec0 -> Spec1 -> Spec2)

## Reference Files

- **`references/refinement-patterns.md`** - Complete refinement mapping patterns (state mapping, history variables, stuttering steps, data/protocol/state machine refinement)
- **`references/checking-refinement.md`** - Verifying refinement with TLC, diagnosing failures, TLC vs TLAPS comparison
- **`references/tlaps-guide.md`** - TLAPS proof system guide (advanced)

## Examples

See `examples/` directory: `AbstractQueue.tla`, `ConcreteQueue.tla`, `QueueRefinement.tla`

## Related Skills

- `tla-model-checking` - Run TLC checks
- `tla-getting-started` - TLA+ basics
- `tla-debug-violations` - Debug counterexamples
- `/tla-check` - Verify refinement
- `/tla-review` - Review refinement structure
