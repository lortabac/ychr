# YCHR

A Constraint Handling Rules (CHR) compiler with multiple backends. The
surface language is standard CHR with Prolog-compatible syntax,
extended with Erlang-style user-defined functions. The compiler is
written in Haskell and lowers programs to a small abstract VM, which
can be interpreted directly or translated to Scheme.

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
[roadmap](https://github.com/lortabac/ychr/blob/master/docs/roadmap.md)
for the full status.

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

`make test` runs the full test suite: the Haskell interpreter, the
Scheme backend and runtime, the REPL, the type checker, the embedding
example, and lint checks over the documentation. Besides GHC it needs
`python3` with `pytest`, and Guile 3.

Compiling to Scheme emits code that imports the YCHR Scheme runtime
(`(ychr runtime)` and friends). That runtime lives in
[`scheme/`](https://github.com/lortabac/ychr/tree/master/scheme)
in this repository and is **not** shipped with the Hackage package, so
`-t scheme` currently requires a source checkout — see the
[Scheme REPL guide](https://github.com/lortabac/ychr/blob/master/docs/how-to/scheme-repl.md).

## Using YCHR as a Haskell library

Compile a `.chr` module from your own program, feed it Haskell values,
decode the answers back.

```
build-depends: ychr
```

```haskell
{-# LANGUAGE OverloadedStrings #-}
import System.IO (hPutStr, stderr)
import YCHR

main :: IO ()
main = do
  result <- compileFiles True ["Order.chr"]
  case result of
    Left err -> hPutStr stderr (displayError err)
    Right (cp, _warnings) -> do
      r <- runQueryCompiled cp goal "R"
      print (r :: Either ConvertError Int)
  where
    goal = CompoundTerm (Unqualified "compute") [VarTerm "R"]
```

Compile once, query `cp` as often as you like. `import YCHR` covers
compiling, querying and marshalling (`ToTerm` / `FromTerm`); Haskell
functions are exposed to CHR as host calls.

- [Embedding a CHR module](https://github.com/lortabac/ychr/blob/master/docs/how-to/embed-a-chr-module.md) —
  worked example: a lambda-calculus type inferencer in CHR, driven from
  Haskell.
- [Value conversion](https://github.com/lortabac/ychr/blob/master/docs/reference/convert.md) —
  `ToTerm` / `FromTerm`, typed queries.
- [Host functions](https://github.com/lortabac/ychr/blob/master/docs/reference/convert.md#registering-host-functions) —
  calling Haskell from CHR.
- [Haskell DSL](https://github.com/lortabac/ychr/blob/master/docs/reference/dsl.md) —
  build programs as Haskell values instead of parsing `.chr` source.

Modules under `YCHR.Internal` are not covered by the package version
policy.

## Documentation

[`docs/`](https://github.com/lortabac/ychr/tree/master/docs) follows
[Diátaxis](https://diataxis.fr/):
[tutorials](https://github.com/lortabac/ychr/tree/master/docs/tutorials),
[how-to guides](https://github.com/lortabac/ychr/tree/master/docs/how-to),
[reference](https://github.com/lortabac/ychr/tree/master/docs/reference)
(language, type system, search, REPL, DSL, conversion, abstract VM) and
[explanation](https://github.com/lortabac/ychr/tree/master/docs/explanation).
Index: [`docs/README.md`](https://github.com/lortabac/ychr/blob/master/docs/README.md).
Status: [`docs/roadmap.md`](https://github.com/lortabac/ychr/blob/master/docs/roadmap.md).
Standard library: [`libraries/`](https://github.com/lortabac/ychr/tree/master/libraries).

Contributor docs:
[`dev-docs/`](https://github.com/lortabac/ychr/tree/master/dev-docs),
starting with
[PROJECT.md](https://github.com/lortabac/ychr/blob/master/dev-docs/PROJECT.md)
(architecture and compilation scheme).

## AI disclosure

This project has been developed with the help of large language models.

## License

BSD-3-Clause
