---
name: tla-getting-started
description: This skill should be used when the user asks to "learn TLA+", "TLA+ tutorial", "get started with TLA+", "first TLA+ spec", "TLA+ basics", "new to TLA+", "TLA+ introduction", or mentions wanting to understand TLA+ fundamentals. Provides introductory guidance for writing first TLA+ specifications.
version: 1.0.0
---

# Getting Started with TLA+

This skill provides introductory guidance for learning TLA+ and writing first specifications. Use this when introducing users to TLA+ concepts and helping them create initial specs.

## What is TLA+?

TLA+ is a formal specification language for designing, modeling, and verifying concurrent and distributed systems. It enables:

- **Modeling system behavior** - Describe how systems evolve over time
- **Finding bugs early** - Discover design flaws before implementation
- **Exhaustive verification** - Check all possible states with TLC model checker
- **Clear documentation** - Specifications serve as precise documentation

## Core Concepts

### State Machines

TLA+ specifications describe state machines:
- **States** - Snapshots of system variables at a point in time
- **Initial states** - Valid starting configurations (Init predicate)
- **Transitions** - How system moves from one state to another (Next action)
- **Behaviors** - Sequences of states following the rules

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

### Key Elements

**Module declaration**: `---- MODULE Name ----` and `====` delimiters

**EXTENDS**: Import standard modules (Naturals, Integers, Sequences, FiniteSets, TLC)

**VARIABLES**: State variables that change over time

**Init predicate**: Defines valid initial states (no primed variables)

**Next action**: Defines state transitions (uses primed variables like `x'`)

**Spec formula**: Combines Init and Next with temporal operators

## First Specification: Counter

Start with a simple counter that increments from 0 to a maximum value.

See `examples/Counter.tla` for a complete working example.

### Step 1: Module and Variables

```tla
---- MODULE Counter ----
EXTENDS Naturals

CONSTANT MaxValue
VARIABLES count
```

**CONSTANT**: Fixed parameters set in configuration file
**VARIABLES**: State that changes during execution

### Step 2: Initial State

```tla
Init == count = 0
```

Define where the system starts. Use `=` for assignment (not `:=`).

### Step 3: Actions

```tla
Increment == count < MaxValue /\ count' = count + 1
ReachMax  == count = MaxValue /\ count' = count
```

**Guard conditions**: Check if action can execute (`count < MaxValue`)
**State updates**: Use primed variables for next state (`count'`)

### Step 4: Next Action

```tla
Next == Increment \/ ReachMax
```

Combine actions with disjunction (`\/`). System can take any enabled action.

### Step 5: Specification

```tla
Spec == Init /\ [][Next]_<<count>>
```

**`[][Next]_<<count>>`**: Next or stuttering (state unchanged)
**Stuttering**: Allows external actions that don't change our variables

### Step 6: Invariants

```tla
TypeInvariant == count \in Nat
BoundInvariant == count <= MaxValue
```

Properties that must hold in every reachable state.

## Running Your First Spec

### Create Configuration File

Create `Counter.cfg` alongside `Counter.tla`:

```
CONSTANT MaxValue = 5
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT BoundInvariant
```

### Parse the Spec

Use MCP tools to validate syntax:

```
sany_parse --file Counter.tla
```

Or use the command: `/tla-parse @Counter.tla`

### Model Check

Run TLC to verify the specification:

```
tlc_check --file Counter.tla
```

Or use the command: `/tla-check @Counter.tla`

### Interpret Results

**Success**: TLC reports "Model checking completed. No errors."
**Failure**: TLC shows counterexample trace violating an invariant

## Common Patterns

### Multiple Variables

```tla
VARIABLES x, y, z

Init == x = 0 /\ y = 0 /\ z = 0

Next == /\ x' = x + 1
        /\ y' = y + x
        /\ UNCHANGED z
```

Use `/\` (conjunction) to combine conditions.
Use `UNCHANGED var` when variable doesn't change.

### Conditional Actions

```tla
Action == IF condition
          THEN /\ x' = value1
               /\ y' = value2
          ELSE /\ x' = value3
               /\ y' = value4
```

### Non-deterministic Choice

```tla
Next == \/ x' = 1 /\ UNCHANGED y
        \/ x' = 2 /\ UNCHANGED y
        \/ y' = 1 /\ UNCHANGED x
```

Multiple actions available - TLC explores all possibilities.

## Best Practices for Beginners

### Start Simple

Begin with minimal specs (1-2 variables, 2-3 actions). Add complexity gradually.

### Name Clearly

Use descriptive names for constants, variables, and actions:
- Good: `MaxClients`, `activeConnections`, `AcceptConnection`
- Avoid: `M`, `x`, `A1`

### Write Invariants Early

Define type invariants first - they catch many errors:

```tla
TypeInvariant == /\ count \in Nat
                 /\ status \in {"idle", "active", "done"}
```

### Comment Complex Logic

Use `\*` for line comments when logic is non-obvious:

```tla
Action == count' = (count + 1) % MaxValue  \* Wrap around at max
```

### Test Incrementally

After each change:
1. Parse with SANY to catch syntax errors
2. Smoke test with TLC to find quick issues
3. Full model check with appropriate bounds

## Common Mistakes

### Forgetting Primed Variables

❌ **Wrong**: `Next == x = x + 1`
✅ **Right**: `Next == x' = x + 1`

In actions, use primes for next-state variables.

### Using Assignment in Init

❌ **Wrong**: `Init == x := 0`
✅ **Right**: `Init == x = 0`

TLA+ uses `=` for equality, not `:=`.

### Missing UNCHANGED

❌ **Wrong**: `Action == x' = x + 1` (What happens to y?)
✅ **Right**: `Action == x' = x + 1 /\ UNCHANGED y`

Specify behavior for all variables.

### Primed Variables in Invariants

❌ **Wrong**: `Invariant == x' > 0`
✅ **Right**: `Invariant == x > 0`

Invariants check current state, not next state.

## Additional Resources

### Reference Files

For detailed syntax and concepts:
- **`references/syntax-basics.md`** - Complete TLA+ syntax reference
- **`references/temporal-operators.md`** - Understanding temporal logic

### Example Specs

Working specifications in `examples/`:
- **`Counter.tla`** - Simple counter with increment
- **`SimpleLock.tla`** - Basic mutual exclusion lock
- **`Counter.cfg`** - Example configuration file

### Knowledge Base

Access knowledge base articles for deeper topics:
- `tla-functions-operators.md` - Functions and operators
- `tla-symbols-set-operations.md` - Set operations and symbols
- `tla-indentation.md` - Indentation and formatting

### MCP Tools

Use these tools for learning:
- `sany_parse` - Validate syntax
- `sany_modules` - List available modules
- `tlc_smoke` - Quick testing (3 seconds)
- `tlc_explore` - Generate example behaviors

### Commands

Available slash commands:
- `/tla-parse` - Parse and validate syntax
- `/tla-smoke` - Quick smoke test
- `/tla-symbols` - Extract symbols and suggest config
- `/tla-setup` - Verify TLA+ tools installation

## Next Steps

After mastering basics:

1. **Learn model checking** - Use the `tla-model-checking` skill for TLC workflows
2. **Study examples** - Read TLA+ examples in the knowledge base
3. **Practice** - Write specs for simple systems (queue, stack, state machine)
4. **Advanced topics** - Explore refinement, temporal properties, and proofs

For comprehensive reviews, use `/tla-review` command to check specifications against best practices.
