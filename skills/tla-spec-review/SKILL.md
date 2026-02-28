---
name: tla-spec-review
description: Use when reviewing TLA+ specifications for correctness, completeness, and best practices. Provides systematic checklist for spec structure, readability, and TLC validation.
---

# TLA+ Specification Review

Use this skill when reviewing TLA+ specifications to ensure correctness, completeness, and adherence to best practices.

## When to Use

- Reviewing a TLA+ specification before model checking
- Code review of TLA+ specs
- Validating spec structure and completeness
- Checking for common TLA+ pitfalls

## Review Checklist

### 1. TLA+ Formulas

- [ ] Check for EXCEPT syntax issues (common mistake: using EXCEPT with wrong structure)
- [ ] Verify all formulas are well-formed
- [ ] Check for proper use of primed variables (x')

### 2. Spec Structure

#### Module Declaration
- [ ] Module name matches filename
- [ ] EXTENDS clauses are necessary and sufficient
- [ ] INSTANCE clauses are used correctly

#### Constants and Assumptions
- [ ] All constants are declared
- [ ] ASSUME statements validate constant constraints
- [ ] Constants have meaningful names

#### Variables
- [ ] All state variables declared in VARIABLES
- [ ] Variables have clear, descriptive names
- [ ] No unnecessary variables

#### Init Predicate
- [ ] Initializes ALL variables
- [ ] Initial state is well-defined
- [ ] No primed variables in Init

#### Next Action
- [ ] Covers all possible state transitions
- [ ] Uses disjunction (\\/) for multiple actions
- [ ] Each action is well-defined
- [ ] Primed variables used correctly

#### Spec Formula
- [ ] Spec == Init /\\ [][Next]_vars /\\ Fairness
- [ ] Fairness conditions appropriate
- [ ] Stuttering allowed where needed

#### Invariants
- [ ] Type invariants defined
- [ ] Safety properties as invariants
- [ ] Invariants are state predicates (no primed variables)

#### Properties
- [ ] Liveness properties defined
- [ ] Temporal formulas correct
- [ ] Properties match requirements

### 3. Readability

- [ ] Consistent indentation
- [ ] Meaningful operator names
- [ ] Comments explain non-obvious logic
- [ ] Complex formulas broken into sub-operators

### 4. TLC Validation

Use MCP tools to validate the spec:

- [ ] **Parse check**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` to verify syntax
- [ ] **Module structure**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_modules` to check dependencies
- [ ] **Symbol resolution**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol` to verify all symbols defined
- [ ] **Smoke test**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke` for quick validation
- [ ] **Model checking**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check` with appropriate config
- [ ] **State exploration**: Use `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_explore` to understand state space

## Common Issues

- **EXCEPT syntax**: `[f EXCEPT ![x] = y]` not `[f EXCEPT [x] = y]`
- **Primed variables**: Only in Next actions, never in Init or Invariants
- **Stuttering**: Ensure `[][Next]_vars` allows stuttering when needed
- **Type invariants**: Define early to catch errors quickly

## MCP Tools Reference

- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse`: Parse and validate TLA+ syntax
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_modules`: Analyze module structure and dependencies
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol`: Look up symbol definitions
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke`: Quick smoke test (small state space)
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check`: Full model checking with config
- `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_explore`: Explore state space interactively
