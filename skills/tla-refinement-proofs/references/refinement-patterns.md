# Refinement Patterns

## Abstract vs. Concrete Specifications

**Refinement** means that a lower-level (concrete/implementation) specification correctly implements the behavior of a higher-level (abstract) specification. Every behavior allowed by the concrete spec must correspond to a behavior allowed by the abstract spec.

- **Abstract spec**: Describes *what* the system should do at a high level
- **Concrete spec**: Describes *how* the system does it with more implementation detail

Refinement is semantic -- it is about the meaning of the specs (their behaviors), not syntax. The specs do not need to share variables or modules.

## The Three WITH Mapping Patterns

When using `INSTANCE` to check refinement, the `WITH` clause defines how concrete state maps to abstract state. There are three patterns:

### Pattern 1: Direct Variable Mapping (WITH)

When the implementation uses different variable names, provide an explicit mapping:

```tla
High == INSTANCE AbstractSpec WITH counter <- x
Refinement == High!Spec
```

Here `counter <- x` maps the abstract variable `counter` to the concrete variable `x`.

### Pattern 2: State Function Mapping (WITH expression)

The mapping can use any state function, not just a single variable:

```tla
High == INSTANCE AbstractSpec WITH counter <- x + y
Refinement == High!Spec
```

This maps `counter` to the computed expression `x + y`.

### Pattern 3: Implicit Mapping (no WITH)

If the concrete module defines a symbol with the same name as in the abstract spec, the mapping is implicit and `WITH` is not required:

```tla
counter == x + y  \* Define counter as a state function

High == INSTANCE AbstractSpec  \* No WITH needed
Refinement == High!Spec
```

Since the concrete module defines `counter` (matching the abstract variable name), no explicit `WITH` clause is needed.

## The PROPERTY Refinement TLC Check Workflow

To verify refinement with TLC:

1. In the concrete spec, instantiate the abstract spec with appropriate mapping:

   ```tla
   Abstract == INSTANCE AbstractSpec WITH abstractVar <- mappingExpr
   Refinement == Abstract!Spec
   ```

2. In the TLC configuration file for the concrete spec, set:

   ```cfg
   SPECIFICATION Spec
   PROPERTY Refinement
   ```

3. Run TLC on the concrete spec:

   ```
   /tla-check ConcreteSpec.tla
   ```

4. If TLC reports no violations, the concrete spec refines the abstract spec.
   If TLC finds a counterexample, the trace shows where refinement breaks.

## Stuttering Steps

TLA+ refinement is **stuttering insensitive**. The concrete spec may have internal actions that are invisible to the abstract spec. These are called stuttering steps.

For example, if the abstract spec has one atomic action:

```tla
Transfer == balance' = balance + amount
```

The concrete spec might split this into multiple steps:

```tla
BeginTransfer == /\ phase' = "pending"
                 /\ UNCHANGED balance
CommitTransfer == /\ balance' = balance + amount
                  /\ phase' = "done"
```

The `BeginTransfer` step does not change the abstract state (`balance`), so it appears as a stuttering step from the abstract spec's perspective. This is valid as long as the observable behavior (changes to `balance`) matches.

The abstract spec does not care *how* the result was achieved, as long as the resulting behavior is the same.

## EXTENDS vs. INSTANCE

Use `EXTENDS` to import definitions directly (like standard modules: Naturals, Sequences). This inlines all operators but can cause name clashes.

Use `INSTANCE` for:
- **Namespacing**: Avoid name clashes with qualified access (`M!Op`)
- **Parameterization**: Substitute CONSTANTS and VARIABLES via `WITH`
- **Refinement**: Map concrete variables to abstract variables
- **Multiple instances**: Create different parameterized versions of the same module

| Use Case                       | EXTENDS | INSTANCE |
|-------------------------------|---------|----------|
| Standard library imports       | Yes     | No       |
| Avoid name clashes            | No      | Yes (qualified access) |
| Module has CONSTANTS          | No      | Yes (WITH) |
| Module has VARIABLES          | No      | Yes (refinement mapping) |
| Multiple parameterized copies | No      | Yes      |
