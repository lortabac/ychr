# YCHR Roadmap

YCHR is a work in progress. This page tracks what is implemented and
what is planned.

## Frontend

- [x] Parser (Prolog-compatible CHR syntax)
- [x] Renaming (module-qualified constraint names)
- [x] Resolution (module flattening, declaration-kind validation)
- [x] Desugaring
- [x] User-defined functions (pattern-matching equations with guards)
- [x] Lambdas and function references

## Compiler

- [x] Head Normal Form transformation
- [x] Occurrence numbering
- [x] CHR-to-VM compilation (refined operational semantics)
- [x] VM serialization
- [ ] Loop-invariant code motion
- [ ] Join ordering
- [x] Late storage
- [ ] Late allocation
- [ ] Guard simplification
- [ ] Set semantics
- [x] Passive occurrences (subsumption/symmetry; see
      [passive-occurrences.md](../dev-docs/passive-occurrences.md))
- [ ] Propagation history elimination
- [ ] Delay avoidance
- [ ] Memory reuse

## Type checker

- [x] Gradual type system core (see [type-system.md](reference/type-system.md))
- [x] Bounded polymorphism
- [x] Exhaustiveness checking for functions over algebraic types
- [x] Guard-derived type evidence — rigid variables at function
      equations and rule-head occurrences, the `GuardMatch`,
      `GuardEqual` and type-predicate evidence forms, and the
      inaccessible-branch warning (`YCHR-20104`); see
      [type-system.md](reference/type-system.md)
- [ ] Refinement-predicate declaration mechanism (replace the
      provisional built-in type-predicate list with a user-extensible
      declaration)
- [ ] Opt-in warning pass flagging doomed uses of `any`-typed values
      via type predicates (bug finding only; never errors)

## Backends

- [x] Haskell interpreter
- [x] Scheme backend
- [x] Scheme runtime
- [ ] JavaScript backend
- [ ] JavaScript runtime

## Runtime (Haskell)

- [x] Logical variables with unification
- [x] Constraint store
- [x] Propagation history
- [x] Reactivation queue
- [x] Store introspection capabilities
- [ ] Meta-programming capabilities

## REPL

- [x] Prolog-style queries
- [x] Live sessions
- [x] Info queries (`:info`, which reports the declared type)
- [x] Tracing

## Testing

- [x] Unit tests (parser, renamer, desugarer, runtime components)
- [x] Golden tests
- [x] End-to-end tests
- [ ] Comprehensive test suite

## Benchmarking

- [x] Interpreter benchmarks
- [ ] Scheme runtime benchmarks
- [ ] JavaScript runtime benchmarks
- [ ] Compiler benchmarks

## Extensions

- [ ] Aggregates, as described in Sneyers, Van Weert, Schrijvers,
      Demoen, 2007. *Aggregates in CHR*.
- [ ] Rule priorities

## Tooling

- [ ] Formatter
- [ ] LSP server

## Development

- [ ] MicroHs compatibility
