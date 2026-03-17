---
title: Choosing Between `CHOOSE` and Non-Determinism in TLA+
description: Understanding the differences between `CHOOSE` and non-determinism in TLA+ specifications.
---

# Choosing Between `CHOOSE` and Non-Determinism in TLA+

In TLA+, both `CHOOSE` and existential quantification (`∃` or `\E`) can express that **some element** with a given property exists. However, they serve **different purposes** and should be used in **different contexts**. `CHOOSE` is constructive—it picks one such element so you can use it as a specific value in definitions, whereas `∃` is logical—it’s used to state that such an element exists, without identifying which one.

## ✅ When to Use `CHOOSE`

- You need to **refer to a specific but arbitrary value** that satisfies a condition.
- You want to **define a function** or variable deterministically based on some property.
- The value must be **stable and consistent** (i.e., the same value is always chosen if the set of satisfying values remains unchanged).

## 🚫 When _Not_ to Use `CHOOSE`

**Do not use `CHOOSE` to eliminate non-determinism** in a behavior specification (i.e. in `Spec`) in order to reduce state space.

> Replacing non-deterministic choices with `CHOOSE` might appear to reduce the number of states, but this is misleading. It’s a bug, not a feature—it changes the meaning of the specification.

CHOOSE is a deterministic choice operator. Given a condition, it selects one specific value that satisfies it—always the same value, as long as the condition and the set of satisfying values don’t change. Mathematicians refer to this idea as Hilbert’s epsilon operator (ε), which denotes "some element" satisfying a property, but in a fixed and consistent way.

### Examples

```tla
CHOOSE x \in Nat : x > 5
```

> Selects **one particular natural number greater than 5**, and always returns the same one as long as the condition doesn’t change.

```tla
NULL ==
    CHOOSE x : x \notin D
```

> Defines a unique value not in the domain `D`—commonly used to model an "uninitialized" or "null" value.

```tla
Max(S) ==
    CHOOSE s \in S: \A t \in S: s >= t
```

> Returns the maximum value from the set `S`. Useful when defining operators that must yield a concrete value.

```tla
\* Assume `S \subseteq DOMAIN func`.
RECURSIVE Sum(_, _)
Sum(func, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  func[x] + Sum(func, S \ {x})
```

> Defines a recursive summation over a set `S` by choosing one element at a time. `CHOOSE` provides a way to select an element from `S` during recursion.

---

## Use Non-Determinism (`∃`, `\/`, etc.) when

- You want to **describe possible behaviors** without specifying **which** value is chosen.
- You are modeling **specifications**, where any value satisfying a condition is acceptable.
- The exact choice doesn’t matter for the correctness of the spec — you care only that **some** value exists.

### Examples

```tla
∃ x \in Nat : x > 5
```

> Asserts that **some** natural number greater than 5 exists — does not specify which.

```tla
CONSTANT T, V
VARIABLE memory
Init ==
   memory \in [T -> V]

WrongInit ==
   memory = [t \in T |-> CHOOSE v \in V: TRUE]
```

> In `Init`, memory is initialized non-deterministically: any mapping from the set of threads `T` to the set of values `V` is valid. In `WrongInit`, memory is initialized to a specific, fixed choice of values—every `t` gets the same deterministically selected `v` from `V`. This restricts behavior and undermines the non-determinism expected in an abstract spec.

```tla
CONSTANT Nodes
VARIABLE inbox
SendMsg(msg) ==
    \E recv \in Nodes:
        inbox' = [inbox EXCEPT ![recv] = @ \cup {msg}]

WrongSendMsg(msg) ==
    LET recv == CHOOSE n \in Node: TRUE
    IN inbox' = [inbox EXCEPT ![recv] = @ \cup {msg}]
```

> In `SendMsg`, the message `msg` may be sent to any node, allowing the spec to explore all possible receivers in the state space. In `WrongSendMsg`, the message is always sent to the same chosen node, reducing the system’s variability and potentially hiding issues that depend on message routing diversity.

This is useful for:

- Abstract specifications
- Modeling non-deterministic or concurrent behavior
- Allowing multiple valid next states in a spec

---

### 📝 Tip

Always ask yourself: **"Do I need to refer to a particular value, or is it enough that such a value exists?"**
