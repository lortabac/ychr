# How to call host-language functions

`host:f(args)` calls a function the runtime provides, not a CHR rule
or a `:- function`. Arguments and result are `any` to the type
checker. Semantics: [language reference](../reference/language.md#host-calls).
Built-in primitives (arithmetic, comparisons, type predicates, term
meta, I/O): [`libraries/prelude.chr`](../../libraries/prelude.chr).

## Register your own

Lift a Haskell function with a `hostFn*` adapter, put it in a
registry, run with a `…WithHostCallRegistry` query. Every name below
comes from `import YCHR`.

```haskell
{-# LANGUAGE OverloadedStrings #-}
import Data.Text (Text)
import YCHR

-- 1. A program that calls host:my_add — compilation does not resolve the
--    name; the registry supplies it at run time.
source :: Text
source =
  ":- chr_constraint compute/2.\n\
  \compute(X, R) <=> R is host:my_add(X, 3).\n"

-- 2. Register the Haskell implementation. hostFn2 marshals the Int
--    arguments and result through ToTerm / FromTerm for you.
registry :: HostCallRegistry
registry = withDefaultHostFunctions
  [ ("my_add", hostFn2 ((+) :: Int -> Int -> Int)) ]

main :: IO ()
main =
  case compileModules stdlib True [("compute.chr", source)] of
    Left err -> putStr (displayError err)
    Right (cp, _warnings) -> do
      -- 3. Run against the custom registry and decode the result.
      r <- runQueryCompiledWithHostCallRegistry registry cp
             (CompoundTerm (Unqualified "compute") [IntTerm 2, VarTerm "R"])
             (decodeVar "R")
      print (r :: Either ConvertError Int)
      -- Right 5
```

(`stdlib` is the parsed standard library — an explicit input of every
compilation. See
[embed-a-chr-module.md §Supplying the resources](embed-a-chr-module.md#5-supplying-the-resources).)

Adapter table, registry semantics, marshalling and errors:
[convert.md §Registering host functions](../reference/convert.md#registering-host-functions).

## On the Scheme backend

There is no registry here. `host:f(X)` compiles to a plain Scheme
call `(f X)`, so `f` must be bound in the generated library. Put it
in a library of your own, `out/my/hosts.sls`:

```scheme
(library (my hosts)
  (export my_add)
  (import (rnrs))
  (define (my_add x y) (+ x y)))
```

and add it to the generated import list with `--import`:

```
$ ychr compile -t scheme -d out --import "(my hosts)" compute.chr
out/ychr/generated/program.sls
$ ychr gen-driver --import "(my hosts)" -g 'compute(2, R)' compute.chr > run.sps
$ scheme --libdirs $YCHR/scheme:out --libexts .sls --program run.sps
R = 5
```

(`$YCHR` is the YCHR source tree; both commands also print a note
about the runtime, left out here.)

`--import` takes one R6RS import set and can be given several times.
Each one is added at the end of the import list. `ychr gen-driver` takes
the same option, for a `host:` call in the goal.

Use `only`, `prefix` or `rename` when names clash. On Chez, a name also
bound by another import (`(rnrs)`, `(ychr runtime)`, and in a driver
`(ychr pretty)` and the generated library) or by the generated code is
an error. Guile lets the later import win, which can break generated
code, so avoid clashes there too.

Without the import, Chez refuses to load the library:

```
Exception: attempt to reference unbound identifier my_add at line 8, char 155 of out/ychr/generated/program.sls
```

Guile loads it and fails only when the call runs. YCHR doesn't check
which names an import provides, so a typo (`host:my_ad(…)`) shows up the
same way.

Limits:

- Only a direct `host:` call reaches an imported procedure. A host term
  built as data and evaluated later (`T = host:my_add(1, 2), R is T`)
  fails with `is: functor is not evaluable`.
- Your procedure gets the arguments only, not the session.
- The Chez REPL (`ychr repl --repl-backend=chez`) has no `--import`.

## Give it a type

A `host:` call is untyped. A `:- function` wrapper types the boundary:

```prolog
:- function my_add(int, int) -> int.
my_add(X, Y) -> host:my_add(X, Y).
```

Callers of `my_add/2` are now checked against `(int, int) -> int`.

## See also

- [Haskell conversion reference](../reference/convert.md)
- [Embed a CHR module in Haskell](embed-a-chr-module.md)
