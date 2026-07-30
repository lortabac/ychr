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

Requires GHC 9.6+ and Cabal 3.4+.

```sh
cabal install ychr
```

To build from a checkout instead:

```sh
make build
make install
```

## Quick start

```sh
ychr repl file.chr                   # interactive REPL (Prolog-style queries)
ychr run -g 'constraint(args)' file  # run a single constraint as the goal
ychr check file.chr                  # type-check only
ychr compile -t scheme -d out file.chr
```

`make test` runs the full test suite (Haskell interpreter, Scheme
backend, REPL, and type-checker tests).

Compiling to Scheme emits code that imports the YCHR Scheme runtime
(`(ychr runtime)` and friends). That runtime lives in [`scheme/`](scheme/)
in this repository and is **not** shipped with the Hackage package, so
`-t scheme` currently requires a source checkout — see the
[Scheme REPL guide](docs/how-to/scheme-repl.md).

## Using YCHR as a Haskell library

YCHR is also an ordinary Haskell library: compile a `.chr` module from
your own program, feed it Haskell values, and decode the answers back.

```
build-depends: ychr
```

```haskell
{-# LANGUAGE OverloadedStrings #-}
import YCHR

main :: IO ()
main = do
  Right (cp, _warnings) <- compileFiles True ["Order.chr"]
  r <- runQueryCompiled cp goal "R"
  print (r :: Either ConvertError Int)
  where
    goal = CompoundTerm (Unqualified "compute") [VarTerm "R"]
```

A single `import YCHR` covers compiling, querying, and marshalling.
Values cross the boundary through the `ToTerm` / `FromTerm` classes, and
Haskell functions can be exposed to CHR programs as host calls.

- [Embedding a CHR module](docs/how-to/embed-a-chr-module.md) — worked
  example: a lambda-calculus type inferencer written in CHR, driven from
  Haskell.
- [Value conversion](docs/reference/convert.md) — `ToTerm` / `FromTerm`,
  decoding, and compile-once/query-many.
- [Host functions](docs/reference/host-functions.md) — calling Haskell
  from CHR.
- [Haskell DSL](docs/reference/dsl.md) — build programs as Haskell values
  instead of parsing `.chr` source.

Modules under `YCHR.Internal` are implementation details and are not
covered by the package version policy.

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

## AI disclosure

This project has been developed with the help of large language models.

## License

BSD-3-Clause
