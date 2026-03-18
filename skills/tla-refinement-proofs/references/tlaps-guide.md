# TLAPS Guide

TLAPS (TLA+ Proof System) enables formal mathematical proofs for TLA+ specifications. Use TLAPS when TLC model checking is insufficient -- for infinite state spaces, unbounded parameters, or when a mathematical proof is required.

## Setup

Enable TLAPS proof strategies by adding to your proof module:

```tla
EXTENDS TLAPS
```

Or alternatively:

```tla
INSTANCE TLAPS
```

This makes proof strategies such as `PTL`, `SMT`, and others available to the prover.

All proofs must be placed in a separate file with the `_proof.tla` extension (e.g., `MyModule_proof.tla`).

## Proof Structure

TLAPS proofs use a hierarchical structure with numbered proof steps.

### ASSUME and Named Assumptions

If your specification includes assumptions using `ASSUME`, name them and explicitly reference them in proofs using the `BY` clause:

```tla
CONSTANT S
ASSUME Assumption == S \subseteq Nat
```

### LEMMA

A lemma states a property to prove. The most common pattern for refinement and invariant proofs:

```tla
LEMMA TypeCorrect == Spec => []TypeOK
```

### Proof Steps

Proofs are structured with numbered levels (`<1>`, `<2>`, etc.):

```tla
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
      BY Assumption DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
      BY Assumption DEF TypeOK, Next, vars, A, B
<1>. QED BY Assumption, <1>1, <1>2, PTL DEF Spec, TypeOK, Init, Next, A, B
```

The pattern for proving an invariant `Inv` holds under specification `Spec`:

1. **Base case** (`<1>1`): Prove `Init => Inv`
2. **Inductive step** (`<1>2`): Prove `Inv /\ [Next]_vars => Inv'`
3. **QED**: Combine using temporal logic (`PTL`)

## Proof Tactics

### OBVIOUS

Used when the proof step is trivially true and the prover can discharge it without additional hints:

```tla
<1>1. 1 + 1 = 2
      OBVIOUS
```

### BY

Explicitly reference facts, assumptions, and definitions the prover needs:

```tla
<1>1. Init => TypeOK
      BY Assumption DEF Init, TypeOK
```

The `BY` clause lists:
- Named assumptions (e.g., `Assumption`)
- Previous proof steps (e.g., `<1>1`, `<1>2`)
- Proof strategies (e.g., `PTL`, `SMT`)

### BY DEF

The `DEF` keyword after `BY` tells TLAPS to expand specific definitions:

```tla
<1>2. TypeOK /\ [Next]_vars => TypeOK'
      BY Assumption DEF TypeOK, Next, vars, A, B
```

This instructs the prover to unfold the definitions of `TypeOK`, `Next`, `vars`, `A`, and `B` during the proof attempt.

### PTL (Propositional Temporal Logic)

Used in QED steps that involve temporal reasoning:

```tla
<1>. QED BY <1>1, <1>2, PTL DEF Spec
```

## Running Proofs

### In VSCode

1. Open the `_proof.tla` file
2. Right-click inside the proof
3. Select "TLA+: Check Prove Step in TLAPS" or use the command palette

### On the Command Line

```bash
opam exec -- tlapm MyModule_proof
```

TLAPS will indicate whether each proof obligation has been successfully discharged or if any have failed. Use this feedback to refine proof steps, adjust assumptions, or restructure arguments.

## Complete Example

```tla
----- MODULE MyModule -----
CONSTANT S
ASSUME Assumption == S \subseteq Nat

VARIABLES x
vars == <<x>>

TypeOK == x \in Nat

Init == x = 0
A == x' = x + 1
B == x' = x
Next == A \/ B

Spec == Init /\ [][Next]_vars
=====

----- MODULE MyModule_proof -----
EXTENDS MyModule, TLAPS

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY Assumption DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY Assumption DEF TypeOK, Next, vars, A, B
<1>. QED BY Assumption, <1>1, <1>2, PTL DEF Spec, TypeOK, Init, Next, A, B
=====
```
