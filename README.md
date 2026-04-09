# YCHR

## Status

Work in progress. Check the roadmap for updates.

## Goal

A production-grade, extensible Constraint Handling Rules (CHR)
compiler targeting dynamically-typed procedural languages.
The surface language is standard CHR with Prolog-compatible syntax.
The compiler is implemented in Haskell and produces code for an internal abstract VM,
which can be interpreted directly or compiled to Scheme or JavaScript.
The VM instructions can also be serialized and fed to another executable to
target different backends.

The compilation algorithm is based on
Peter Van Weert, Pieter Wuille, Tom Schrijvers, Bart Demoen, 2008.
"_CHR for Imperative Host Languages_."

## Differences from K.U.Leuven CHR

### Functions

When CHR is embedded in Prolog, guards can rely on predicate success or failure.

In YCHR, instead, guards are functional expressions that return a boolean value.
They can be calls to procedures in the host language or user-defined *functions*.
*Functions* are a simple extension to CHR. They have Erlang-like syntax
and work by top-to-bottom pattern-matching.

Example:

```
:- function member/2.

member(_, []) -> false.
member(X, [X|_]) -> true.
member(X, [_|Xs]) -> member(X, Xs).
```

### is

The `is` operator is generalized to accept any expression on the RHS,
including CHR functions and host language function calls.

Example:

```
ychr> R is member(1, [0, 1, 2]).
R = true.
```

## Roadmap

### Frontend

- [x] Parser (Prolog-compatible CHR syntax)
- [x] Renaming (module-qualified constraint names)
- [x] Desugaring
- [x] User-defined functions (pattern-matching equations with guards)
- [x] Lambdas and function references

### Compiler

- [x] Head Normal Form transformation
- [x] Occurrence numbering
- [x] CHR-to-VM compilation (refined operational semantics)
- [x] VM serialization
- [ ] Loop-invariant code motion
- [ ] Join ordering
- [ ] Late storage
- [ ] Late allocation
- [ ] Guard simplification
- [ ] Set semantics
- [ ] Passive occurrences
- [ ] Propagation history elimination
- [ ] Delay avoidance
- [ ] Memory reuse

### Type checker

- [ ] Gradual type system
- [ ] Simple type refinements via type predicates

### Backends

- [x] Haskell interpreter
- [ ] Scheme backend
- [ ] Scheme runtime
- [ ] JavaScript backend
- [ ] JavaScript runtime

### Runtime (Haskell)

- [x] Logical variables with unification
- [x] Constraint store
- [x] Propagation history
- [x] Reactivation queue
- [ ] Introspection capabilities
- [ ] Meta-programming capabilities

### REPL

- [x] Prolog-style queries
- [ ] Store inpection
- [ ] Live debugging sessions

### Testing

- [x] Unit tests (parser, renamer, desugarer, runtime components)
- [x] Golden tests
- [x] End-to-end tests
- [ ] Comprehensive test suite

### Benchmarking

- [ ] Interpreter benchmarks
- [ ] Scheme runtime benchmarks
- [ ] JavaScript runtime benchmarks
- [ ] Compiler benchmarks

## Installation

Requires GHC 9.12+ and Cabal 3.4+.

```sh
cabal build
cabal install
```

## Usage

### REPL

```sh
ychr repl file.chr
```

Inside the REPL, enter a Prolog-style query and press Enter. For example:

```
ychr> factorial(10, X), Y is X + 1.
```

Type `:help` for available commands.

### Run a goal

Run a single goal non-interactively:

```sh
ychr run -g 'leq(1, 2)' file.chr
```

### Run tests

```sh
cabal test
```

## License

BSD-3-Clause
