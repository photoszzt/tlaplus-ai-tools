---
name: tla-getting-started
description: >-
  This skill provides introductory guidance for learning TLA+ and writing first specifications.
  It should be used when the user asks to "learn TLA+", "what is TLA+", "TLA+ tutorial",
  "get started with TLA+", "first TLA+ spec", "TLA+ basics", "new to TLA+",
  "TLA+ introduction", "how to write TLA+", "TLA+ help", "TLA+ example", "write a spec", "TLA+ spec template",
  "formal specification", "create a spec", "model a system",
  or the user mentions wanting to understand TLA+ fundamentals.
version: 1.0.0
allowed-tools:
  - Read
---

# Getting Started with TLA+

Introductory guidance for learning TLA+ and writing first specifications.

## What is TLA+?

TLA+ is a formal specification language for designing, modeling, and verifying concurrent and distributed systems. It enables modeling system behavior, finding bugs early through exhaustive verification, and serving as precise documentation. In practice, TLA+ is used to find concurrency bugs before writing code and to verify the correctness of distributed protocols, saving significant debugging time in production systems.

## Core Concepts

### State Machines

TLA+ specifications describe state machines with **states** (variable snapshots), **initial states** (Init predicate), **transitions** (Next action), and **behaviors** (sequences of states).

### Specification Structure

Every TLA+ spec follows this pattern:

```tla
---- MODULE SpecName ----
EXTENDS Naturals         \* Import standard modules
VARIABLES x, y           \* Declare state variables

Init == x = 0 /\ y = 0   \* Initial state
Next == x' = x + 1       \* State transitions
     /\ y' = y + x

Spec == Init /\ [][Next]_<<x,y>>  \* Complete specification
====
```

**Key elements**: Module declaration (`---- MODULE Name ----` / `====`), `EXTENDS` for imports, `VARIABLES` for state, Init (no primes), Next (uses `x'` for next-state), Spec formula combining Init and Next.

## First Specification: Counter

```tla
---- MODULE Counter ----
EXTENDS Naturals
CONSTANT MaxValue
VARIABLES count

Init == count = 0
Increment == count < MaxValue /\ count' = count + 1
ReachMax  == count = MaxValue /\ count' = count
Next == Increment \/ ReachMax

TypeInvariant == count \in Nat
BoundInvariant == count <= MaxValue

Spec == Init /\ [][Next]_<<count>>
====
```

**Configuration file** (`Counter.cfg`):

```
CONSTANT MaxValue = 5
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT BoundInvariant
```

## Running Your First Spec

1. **Parse**: `/tla-parse @Counter.tla` - validate syntax
2. **Smoke test**: `/tla-smoke @Counter.tla` - quick 3-second check
3. **Full check**: `/tla-check @Counter.tla` - exhaustive model checking

**Success**: TLC reports "Model checking completed. No errors."
**Failure**: TLC shows counterexample trace violating an invariant.

## Best Practices for Beginners

- **Start simple**: 1-2 variables, 2-3 actions. Add complexity gradually.
- **Name clearly**: `MaxClients`, `activeConnections`, `AcceptConnection` (not `M`, `x`, `A1`)
- **Write invariants early**: Type invariants catch many errors.
- **Test incrementally**: Parse, smoke test, then full model check after each change.

## Common Mistakes

- **Forgetting primes**: `x' = x + 1` not `x = x + 1` in actions
- **Wrong assignment in Init**: Use `x = 0` not `x := 0`
- **Missing UNCHANGED**: Specify behavior for all variables in every action
- **Primed variables in invariants**: Invariants check current state (`x > 0` not `x' > 0`)

See `references/syntax-basics.md` for the complete syntax reference covering operators, data types, standard modules, and common code patterns.

## Example Specs

Working specifications in `examples/`: `Counter.tla`, `SimpleLock.tla`, `Counter.cfg`

## Next Steps

1. **Learn model checking** - Use the `tla-model-checking` skill
2. **Study examples** - Read TLA+ examples in the knowledge base
3. **Practice** - Write specs for simple systems (queue, stack, state machine)
4. **Advanced topics** - Explore refinement, temporal properties, and proofs

## Related Skills

- `/tla-parse` - Parse and validate syntax
- `/tla-smoke` - Quick smoke test
- `/tla-symbols` - Extract symbols and suggest config
- `/tla-check` - Full model checking
- `/tla-review` - Check specs against best practices
