# A CHR Primer

> **Audience:** readers new to Constraint Handling Rules.
> **You will:** learn what CHR is, what a rule does, and how a program runs.
> **Skip if:** you already know CHR — go to
> [your first program](03-your-first-program.md).

This page is a stub. The eventual flow:

## What is CHR?

Constraint Handling Rules is a rule-based language whose state is a
*multiset of constraints* called the **constraint store**. A program is a
collection of rules that rewrite the store.

## The three rule kinds

- **Simplification** (`<=>`): removes the matched constraints and replaces
  them with the rule body.
- **Propagation** (`==>`): keeps the matched constraints and adds the rule
  body.
- **Simpagation** (`\`): keeps the constraints to the left of `\`, removes
  the ones to the right, and adds the body.

## A worked example

> **TODO:** walk through a concrete trace of `leq` with several goals,
> showing the store before and after each fire.

## Guards

> **TODO:** explain that guards are pure tests; they cannot bind variables;
> contrast with `=` in the body.

## Termination, confluence, and the firing order

> **TODO:** brief, conceptual: rules fire under the *refined operational
> semantics*, top-to-bottom by occurrence, with a propagation history that
> prevents the same propagation from firing twice on the same combination.
> Cross-link to [explanation/operational-semantics.md](../explanation/operational-semantics.md).

## Next

- [Your first YCHR program](03-your-first-program.md).
- Pure conceptual reading: [What is CHR?](../explanation/what-is-chr.md).
