# YCHR

A Constraint Handling Rules (CHR) compiler with multiple backends. The
surface language is standard CHR with Prolog-compatible syntax,
extended with Erlang-style user-defined functions. The compiler is
written in Haskell and lowers programs to a small abstract VM, which
can be interpreted directly or translated to Scheme or JavaScript.

The compilation algorithm follows Van Weert, Wuille, Schrijvers, and
Demoen (2008), *CHR for Imperative Host Languages*.

## Example

```prolog
:- module(order, [leq/2]).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

```sh
$ ychr run -g 'leq(1, X), leq(X, 1)' leq.chr
```

## Status

Work in progress. The Haskell interpreter and Scheme backend are
working; the JavaScript backend and most of the optimization catalogue
from the paper are not yet implemented. See
[docs/roadmap.md](docs/roadmap.md) for the full status.

## Install

Requires GHC 9.12+ and Cabal 3.4+.

```sh
make build
make install
```

## Quick start

```sh
ychr repl file.chr           # interactive REPL (Prolog-style queries)
ychr run -g 'goal(...)' file # run a single goal
ychr check file.chr          # type-check only
ychr compile --target=scheme -o out file.chr
```

`make test` runs the full test suite (Haskell interpreter, Scheme
backend, REPL, and type-checker tests).

## Documentation

- [docs/language.md](docs/language.md) — language reference
  (modules, functions, `is`, lambdas)
- [docs/type-system.md](docs/type-system.md) — optional gradual type
  system
- [docs/vm.md](docs/vm.md) — abstract VM specification and
  s-expression serialization format (for backend implementors)
- [docs/roadmap.md](docs/roadmap.md) — implementation status

Contributor and design documentation lives in [`dev-docs/`](dev-docs/),
including [PROJECT.md](dev-docs/PROJECT.md) (architecture and
compilation scheme) and the reference paper.

## License

BSD-3-Clause
