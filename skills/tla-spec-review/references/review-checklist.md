# TLA+ Specification Review Checklist

Comprehensive checklist for reviewing TLA+ specifications.

## Module Structure

### Module Declaration
- [ ] Module name matches filename
- [ ] Proper delimiters: `---- MODULE Name ----` and `====`
- [ ] No content before first delimiter
- [ ] No content after last delimiter

### EXTENDS and INSTANCE
- [ ] All EXTENDS modules are necessary
- [ ] No unnecessary standard modules imported
- [ ] INSTANCE used correctly with WITH substitutions
- [ ] Instantiated modules exist and are accessible

## Declarations

### Constants
- [ ] All constants declared with CONSTANT
- [ ] Constant names are clear and descriptive
- [ ] ASSUME statements validate constant constraints
- [ ] ASSUME conditions are satisfiable

### Variables
- [ ] All state variables declared with VARIABLES
- [ ] Variable names are clear and descriptive
- [ ] No unnecessary variables
- [ ] Variables represent mutable state (not derived values)

## Init Predicate

- [ ] Initializes ALL declared variables
- [ ] No primed variables (x') in Init
- [ ] Initial state is well-defined and unambiguous
- [ ] Init is satisfiable (not contradictory)
- [ ] Uses = for assignment, not :=

## Actions and Next

### Individual Actions
- [ ] Each action is well-formed
- [ ] Guard conditions prevent invalid transitions
- [ ] All variables have next-state values (x')
- [ ] UNCHANGED used for variables that don't change
- [ ] No circular dependencies in assignments

### Next Predicate
- [ ] Covers all intended state transitions
- [ ] Uses disjunction (\/) for alternative actions
- [ ] No unreachable actions
- [ ] Terminates appropriately (or intended infinite)

### Primed Variables
- [ ] Primed variables only in actions (Next)
- [ ] No primed variables in Init
- [ ] No primed variables in invariants
- [ ] Primed variables used consistently

## Specification Formula

- [ ] Follows pattern: `Init /\ [][Next]_vars`
- [ ] Stuttering allowed where appropriate (uses [A]_v not <<A>>_v)
- [ ] Fairness conditions appropriate for system
- [ ] Weak fairness (WF) vs strong fairness (SF) chosen correctly
- [ ] Variables tuple complete: `<<var1, var2, var3>>`

## Invariants

### Type Invariants
- [ ] Type invariant defined (TypeInvariant or TypeOK)
- [ ] Covers all variables
- [ ] Precise type specifications
- [ ] No primed variables

### Safety Invariants
- [ ] Safety properties expressed as invariants
- [ ] Invariants are state predicates
- [ ] Invariants are not too weak (catch violations)
- [ ] Invariants are not too strong (provable)
- [ ] Clear and descriptive names

## Temporal Properties

- [ ] Liveness properties defined as PROPERTY
- [ ] Temporal operators used correctly ([], <>, ~>)
- [ ] Properties match requirements
- [ ] Fairness needed for liveness
- [ ] Property names descriptive

## Operators and Functions

- [ ] Operators have clear purposes
- [ ] Parameters well-typed
- [ ] Recursive operators have base cases
- [ ] Helper operators simplify main definitions
- [ ] Function domains specified correctly

## EXCEPT Syntax

- [ ] Uses correct syntax: `[f EXCEPT ![x] = y]` (with !)
- [ ] Not incorrect: `[f EXCEPT [x] = y]` (without !)
- [ ] Multiple updates use correct chaining
- [ ] Record updates use .field: `[r EXCEPT !.field = v]`

## Sets and Sequences

- [ ] Set operations used appropriately
- [ ] Sequence indexing within bounds
- [ ] Cardinality constraints clear
- [ ] SUBSET used correctly for power sets
- [ ] Set comprehensions well-formed

## Style and Readability

### Naming
- [ ] Constants: UPPER_CASE or CamelCase
- [ ] Variables: camelCase or lowercase
- [ ] Operators: CamelCase
- [ ] Names descriptive, not cryptic (avoid x, y, z, a, b)

### Formatting
- [ ] Consistent indentation (2 or 4 spaces)
- [ ] Aligned conjunctions (/\) and disjunctions (\/)
- [ ] Reasonable line length (<100 characters)
- [ ] Blank lines separate major sections

### Comments
- [ ] Complex logic has explanatory comments
- [ ] Module has overview comment
- [ ] Non-obvious design decisions documented
- [ ] Comments use \* for line, (* *) for block

### Complexity
- [ ] Complex expressions broken into sub-operators
- [ ] Deeply nested expressions avoided
- [ ] Repeated patterns extracted to operators
- [ ] Spec is understandable by others

## Configuration Readiness

- [ ] Can generate valid TLC configuration
- [ ] Constants can be assigned reasonable values
- [ ] Model checking is feasible (state space manageable)
- [ ] Smoke test runs successfully

## Common Pitfalls Checked

- [ ] No assignment operator (:=) used
- [ ] No primed variables in wrong places
- [ ] No EXCEPT without !
- [ ] No missing UNCHANGED
- [ ] No unguarded actions (too permissive)
- [ ] No infinite loops without intention
- [ ] No undefined symbols
- [ ] No type mismatches

## Best Practices

- [ ] Follows TLA+ conventions
- [ ] Similar to well-known specifications
- [ ] Uses standard modules appropriately
- [ ] Gradual complexity (simple base, complex on top)
- [ ] Testable incrementally

## Final Checks

- [ ] Parses successfully with SANY
- [ ] Passes smoke test
- [ ] Configuration file exists or can be generated
- [ ] Documentation adequate for maintenance
- [ ] Ready for model checking

Use this checklist systematically. Don't skip sections even if they seem obvious - catching issues early saves time debugging later.
