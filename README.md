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
$ ychr repl examples/leq.chr
ychr> leq(X, Y), leq(Y, X).
X = Y,
Y = X.
ychr>
```

## Status

Work in progress. The Haskell interpreter and Scheme backend are
working; the JavaScript backend and most of the optimization catalogue
from the paper are not yet implemented. See the
[roadmap](docs/roadmap.md) for the full status.

## Install

Requires GHC 9.12+ and Cabal 3.4+.

```sh
make build
make install
```

## Quick start

```sh
ychr repl file.chr           # interactive REPL (Prolog-style queries)
ychr run -g 'constraint(args)' file # run a single constraint as the goal
ychr check file.chr          # type-check only
ychr compile --target=scheme -o out file.chr
```

`make test` runs the full test suite (Haskell interpreter, Scheme
backend, REPL, and type-checker tests).

## Documentation

User-facing documentation lives in [`docs/`](docs/) and follows the
[Diátaxis](https://diataxis.fr/) structure:

- [Tutorials](docs/tutorials/) — getting started, CHR primer, your first
  program.
- [How-to guides](docs/how-to/) — REPL, types, host calls, modules.
- [Reference](docs/reference/) — language, syntax, type system, prelude,
  CLI, REPL, errors, abstract VM.
- [Explanation](docs/explanation/) — what CHR is, operational semantics,
  design rationale.

See [`docs/README.md`](docs/README.md) for a full index with reading
paths for newcomers and existing CHR/Prolog users, and
[`docs/roadmap.md`](docs/roadmap.md) for implementation status.

Contributor and design documentation lives in [`dev-docs/`](dev-docs/),
including [PROJECT.md](dev-docs/PROJECT.md) (architecture and
compilation scheme) and the reference paper.

## License

BSD-3-Clause
