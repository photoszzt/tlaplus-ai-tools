---
name: tla-refinement-proofs
description: This skill should be used when the user asks about "refinement", "specification refinement", "refine specification", "abstract and concrete specs", "implementation correctness", or mentions proving one spec implements another.
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

**Refinement** proves that a concrete (implementation) specification correctly implements an abstract (high-level) specification.

**Key idea**: Every behavior allowed by the concrete spec corresponds to a behavior allowed by the abstract spec.

### Why Refine?

1. **Layered Design** - Build complex systems incrementally
2. **Verified Implementation** - Prove code matches design
3. **Optimization Verification** - Prove optimized version correct
4. **Interface Compliance** - Prove component implements interface

## Types of Refinement

### Safety Refinement

Concrete spec's behaviors are subset of abstract spec's behaviors.

**Checked with TLC**:
- Define refinement mapping
- Check concrete implements abstract

### Liveness Refinement

Concrete spec satisfies abstract spec's liveness properties.

**Requires**:
- Safety refinement
- Fairness conditions

## Refinement Workflow with TLC

### 1. Create Abstract Specification

High-level design:
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

Implementation with more detail:
```tla
---- MODULE ConcreteCounter ----
EXTENDS Naturals
VARIABLES x, y  \* Implementation uses two variables

Init == x = 0 /\ y = 0
IncX == x' = x + 1 /\ UNCHANGED y
IncY == y' = y + 1 /\ UNCHANGED x

Spec == Init /\ [][IncX \/ IncY]_<<x,y>>
====
```

### 3. Define Refinement Mapping

Map concrete state to abstract state:
```tla
count == x + y  \* How concrete variables relate to abstract
```

### 4. Check Refinement with TLC

**Method 1: INSTANCE with substitution**

In concrete spec:
```tla
A == INSTANCE AbstractCounter WITH count <- x + y

THEOREM Spec => A!Spec
```

**Method 2: Separate refinement module**

```tla
---- MODULE CheckRefinement ----
EXTENDS Naturals

VARIABLES x, y

C == INSTANCE ConcreteCounter
A == INSTANCE AbstractCounter WITH count <- x + y

Spec == C!Spec

\* Check abstract spec properties hold
THEOREM Spec => A!Spec
THEOREM Spec => A!Init
THEOREM Spec => [][A!Inc]_<<x,y>>
====
```

**TLC Configuration**:
```
SPECIFICATION Spec
INVARIANT A!TypeInvariant
PROPERTY A!LivenessProperty
```

### 5. Run TLC to Verify

```
/tla-check @CheckRefinement.tla
```

If passes: Concrete refines abstract ✓

If fails: Trace shows where refinement breaks ✗

## Refinement Mapping

### State Mapping

Define how concrete variables map to abstract:

**Simple mapping**:
```tla
abstractVar == concreteVar
```

**Computed mapping**:
```tla
count == x + y
status == IF phase = "init" THEN "idle" ELSE "active"
```

**Set projection**:
```tla
items == {msg.data : msg \in messages}
```

### History Variables

Sometimes need extra state to establish refinement:

```tla
VARIABLES state, history  \* history is history variable

\* Track events for refinement
UpdateHistory == history' = Append(history, state)
```

### Stuttering Steps

Concrete may have internal actions invisible to abstract:

```tla
\* Abstract sees one step
AbstractAction == x' = x + 1

\* Concrete may take multiple steps
ConcreteAction1 == temp' = x + 1 /\ UNCHANGED x
ConcreteAction2 == x' = temp /\ UNCHANGED temp

\* Map both to abstract step via stuttering
```

## Common Refinement Patterns

### Data Refinement

Abstract set becomes concrete sequence:
```tla
\* Abstract
VARIABLE items  \* Set of items

\* Concrete
VARIABLE queue  \* Sequence of items

\* Mapping
items == {queue[i] : i \in 1..Len(queue)}
```

### Protocol Refinement

Abstract atomic action becomes multi-step protocol:
```tla
\* Abstract
Transfer(a, b, amt) ==
    /\ balance[a]' = balance[a] - amt
    /\ balance[b]' = balance[b] + amt

\* Concrete (with commit protocol)
BeginTransfer(a, b, amt) == ...
CommitTransfer == ...
AbortTransfer == ...
```

### State Machine Refinement

Abstract states map to concrete states:
```tla
\* Abstract: {idle, busy}
\* Concrete: {init, working, finalizing}

\* Mapping
status == CASE state \in {"init"} -> "idle"
            [] state \in {"working", "finalizing"} -> "busy"
```

## Checking Refinement

### Invariant Checking

Abstract invariants should hold on concrete:

```
\* In concrete config
INVARIANT
    AbstractSpec!TypeInvariant
    AbstractSpec!SafetyProperty
```

### Trace Checking

If refinement fails:
1. TLC shows counterexample
2. Trace shows concrete behavior
3. Find where abstract property violated
4. Fix concrete spec or refinement mapping

### Common Failures

**Wrong mapping**:
```
count == x * y  \* Should be x + y
```
Fix: Correct the mapping function.

**Missing initialization**:
```
\* Abstract: x = 0
\* Concrete: forgot to set something
```
Fix: Initialize all concrete state.

**Extra behaviors**:
```
\* Concrete allows actions abstract doesn't
```
Fix: Strengthen concrete guards or abstract spec.

## TLC-Based vs TLAPS Proofs

### TLC (Model Checking)

✅ **Pros**:
- Automatic verification
- Finds counterexamples
- Easy to use

❌ **Cons**:
- Finite state spaces only
- Not a mathematical proof
- Bounded checking

**When to use**: Most practical refinement checking.

### TLAPS (Proof System)

✅ **Pros**:
- Mathematical proofs
- Works for infinite state spaces
- Complete verification

❌ **Cons**:
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

See `references/tlaps-guide.md` for TLAPS details (advanced).

## Best Practices

### Start Simple

1. Verify simple property first
2. Check type refinement
3. Add safety properties
4. Finally liveness

### Modular Refinement

Chain refinements:
```
Spec1 refines Spec0 (high-level)
Spec2 refines Spec1 (medium-level)
Spec3 refines Spec2 (implementation)
```

### Document Mapping

Comment refinement mapping clearly:
```tla
\* Refinement Mapping:
\* Abstract 'count' represents total items
\* Concrete 'x + y' splits count into two counters
count == x + y
```

### Test Mapping

Before checking refinement:
```
1. Check concrete spec correct on its own
2. Verify mapping makes sense
3. Check abstract spec still makes sense
```

## Examples

See `examples/` directory:
- `AbstractQueue.tla` - Simple abstract queue
- `ConcreteQueue.tla` - Implementation with array
- `QueueRefinement.tla` - Refinement proof

## Additional Resources

### Reference Files

- **`references/refinement-patterns.md`** - Common refinement patterns
- **`references/tlaps-guide.md`** - TLAPS proof system (advanced)

### Knowledge Base

- `tla-refinement.md` - Detailed refinement guide
- `tla-different-configurations.md` - Multiple configuration patterns

### Related Skills

- `tla-model-checking` - Run TLC checks
- `tla-getting-started` - TLA+ basics
- `tla-spec-review` - Review specifications

### Related Commands

- `/tla-check` - Verify refinement
- `/tla-review` - Review refinement structure

## Quick Reference

```tla
\* Pattern for refinement checking

---- MODULE Concrete ----
VARIABLES ...concrete vars...

ConcreteInit == ...
ConcreteNext == ...
ConcreteSpec == ConcreteInit /\ [][ConcreteNext]_vars

\* Instance of abstract spec with mapping
A == INSTANCE Abstract WITH
    abstractVar <- mappingExpression

\* Properties to check
THEOREM ConcreteSpec => A!Spec
THEOREM ConcreteSpec => A!Property
====
```

```
\* TLC Config
SPECIFICATION ConcreteSpec
INVARIANT A!Invariant
PROPERTY A!Property
```

Refinement enables compositional reasoning - verify each level independently, prove levels relate correctly.
