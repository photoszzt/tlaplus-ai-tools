# TLA+ Syntax Basics

Complete reference for TLA+ syntax and operators.

## Module Structure

```tla
----MODULE ModuleName ----
[EXTENDS modules]
[CONSTANTS symbols]
[ASSUME assumptions]
[VARIABLES symbols]
[definitions]
====
```

## Operators

### Logic Operators

- `~P` or `\neg P` or `\lnot P` - NOT
- `P /\ Q` - AND (conjunction)
- `P \/ Q` - OR (disjunction)
- `P => Q` - IMPLIES
- `P <=> Q` or `P \equiv Q` - EQUIVALENCE

### Comparison

- `e = f` - Equality
- `e # f` or `e /= f` - Inequality
- `e < f`, `e > f` - Less than, greater than
- `e <= f` or `e \leq f` - Less than or equal
- `e >= f` or `e \geq f` - Greater than or equal

### Arithmetic

- `e + f` - Addition
- `e - f` - Subtraction
- `e * f` - Multiplication
- `e \div f` - Integer division
- `e % f` - Modulo
- `e^f` - Exponentiation

### Set Operators

- `e \in S` - Element of
- `e \notin S` - Not element of
- `S \cup T` or `S \union T` - Union
- `S \cap T` or `S \inter T` - Intersection
- `S \ T` or `S \setminus T` - Set difference
- `S \subseteq T` - Subset or equal
- `SUBSET S` - Set of all subsets
- `UNION S` - Union of sets in S
- `{e : x \in S}` - Set comprehension
- `{x \in S : P}` - Set filter

### Quantifiers

- `\A x \in S : P` - Universal (for all)
- `\E x \in S : P` - Existential (there exists)
- `CHOOSE x \in S : P` - Choose one element satisfying P

### Temporal Operators

- `[]P` - Always P (globally)
- `<>P` - Eventually P (finally)
- `[A]_v` - A or variables v unchanged
- `<<A>>_v` - A and variables v changed
- `WF_v(A)` - Weak fairness
- `SF_v(A)` - Strong fairness
- `P ~> Q` - P leads to Q

### State Relations

- `x'` - Value of x in next state
- `UNCHANGED <<x, y>>` - Variables unchanged
- `x' = e` - x has value e in next state

### Conditional

- `IF P THEN e1 ELSE e2`
- `CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3`

### Let Definitions

```tla
LET x == expression
    y == expression
IN body
```

## Data Types

### Booleans

- `TRUE`, `FALSE`
- `BOOLEAN` - Set {TRUE, FALSE}

### Numbers

- `Nat` - Natural numbers {0, 1, 2, ...}
- `Int` - Integers {..., -1, 0, 1, ...}
- `Real` - Real numbers
- `a..b` - Range from a to b

### Strings

- `"text"` - String literal
- `STRING` - Set of all strings

### Sequences

- `<<a, b, c>>` - Sequence literal
- `Len(seq)` - Length
- `seq[i]` - Element at index i (1-based)
- `Append(seq, e)` - Append element
- `Head(seq)` - First element
- `Tail(seq)` - All but first
- `SubSeq(seq, m, n)` - Subsequence
- `seq \o t` or `seq \circ t` - Concatenation

### Records

- `[field1 |-> value1, field2 |-> value2]` - Record literal
- `r.field` or `r["field"]` - Field access
- `[r EXCEPT !.field = value]` - Update field
- `[field1: S1, field2: S2]` - Set of all records

### Functions

- `[x \in S |-> expression]` - Function definition
- `f[x]` - Function application
- `DOMAIN f` - Domain of function
- `[f EXCEPT ![x] = e]` - Update function
- `[S -> T]` - Set of functions from S to T

## Common Patterns

### Initializing Multiple Variables

```tla
Init == /\ x = 0
        /\ y = 0
        /\ status = "idle"
```

### Disjunctive Actions

```tla
Next == \/ Action1
        \/ Action2
        \/ Action3
```

### Conjunctive Constraints

```tla
Action == /\ condition1
          /\ condition2
          /\ x' = newValue
```

### Non-Deterministic Choice

```tla
Action == \E v \in Values :
    /\ x' = v
    /\ UNCHANGED y
```

### Updating Records

```tla
UpdateField(r, newValue) ==
    [r EXCEPT !.field = newValue]
```

### Updating Functions

```tla
UpdateKey(f, key, value) ==
    [f EXCEPT ![key] = value]
```

### Sequence Operations

```tla
\* Add to end
AddToSeq(seq, elem) == Append(seq, elem)

\* Add to front
Prepend(seq, elem) == <<elem>> \o seq

\* Remove first occurrence
RemoveFirst(seq, elem) ==
    LET i == CHOOSE j \in 1..Len(seq) : seq[j] = elem
    IN SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))
```

## Standard Modules

### Naturals
- `Nat` - Natural numbers
- `+`, `-`, `*`, `\div`, `%`, `^`
- `a..b` - Range

### Integers
- `Int` - All integers
- All Naturals operators
- Negative numbers

### Sequences
- `Seq(S)` - All sequences over S
- `Len`, `Head`, `Tail`, `Append`, `\o`
- `SubSeq`, sequence comprehensions

### FiniteSets
- `Cardinality(S)` - Size of set
- `IsFiniteSet(S)` - Check if finite

### TLC
- `Print(out, val)` - Print and return val
- `Assert(condition, message)` - Runtime assertion
- `JavaTime` - Current time in ms
- `ToString(val)` - Convert to string
- `:>` - Function constructor

### Bags (multisets)
- `IsABag(B)` - Check if bag
- `BagToSet(B)` - Convert to set
- `SetToBag(S)` - Convert to bag
- `BagIn(x, B)` - Element in bag

### RealTime
- Real-time specifications
- Time-bounded properties

## Comments

- `\*` - Line comment
- `(* multi-line comment *)`

## Naming Conventions

- **Constants**: UPPER_CASE or CamelCase
- **Variables**: camelCase or snake_case
- **Operators**: CamelCase or camelCase
- **Actions**: CamelCase (verb-noun)
- **Predicates**: CamelCase or lowercase

## Formatting

- **Indentation**: 2 or 4 spaces
- **Alignment**: Align `/\` and `\/`
- **Spacing**: Space around operators
- **Line length**: Keep under 80-100 characters

## Precedence (high to low)

1. Function application, subscript, field access
2. Unary minus, domain, prefix operators
3. Exponentiation `^`
4. Multiplication `*`, division `\div`, modulo `%`
5. Addition `+`, subtraction `-`, set operators
6. Comparison `<`, `>`, `<=`, `>=`, `\in`, `\subseteq`
7. Equality `=`, inequality `#`
8. Negation `~`, `\neg`
9. Conjunction `/\`
10. Disjunction `\/`
11. Implication `=>`
12. Equivalence `<=>`, `\equiv`
13. Temporal operators `[]`, `<>`, `~>`
14. Quantifiers `\A`, `\E`

Use parentheses for clarity when precedence is unclear.
