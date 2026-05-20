# How to drive a compiled CHR program from a Scheme REPL

> **Goal:** compile a CHR program once with `ychr compile -t scheme`,
> then poke at it interactively from Chez (or Guile) without
> hand-writing a driver script.

The umbrella `(ychr)` library bundles the runtime plus the helpers
`open-session` and `query`, so a typical session is three user lines
after the imports.

## 1. Compile the program

Pass `-n NAME` to give the generated library a friendly name (the
identifier you'll use to open a session). Without `-n`, the binding is
just `program`.

```sh
ychr compile -t scheme -n fib -d /tmp/fib-repl test/golden/fib/fib.chr
# → /tmp/fib-repl/ychr/generated/fib.sls
```

## 2. Start the REPL with both library trees on the search path

```sh
scheme --libdirs PROJECT_ROOT/scheme:/tmp/fib-repl --libexts .sls
```

- The first `--libdirs` entry holds the YCHR runtime (`scheme/ychr/`).
- The second holds the freshly compiled program
  (`/tmp/fib-repl/ychr/generated/fib.sls`).
- `--libexts .sls` tells Chez to recognize the `.sls` extension R6RS
  libraries ship with.

Guile works too — substitute `guile3.0 -L PROJECT_ROOT/scheme -L /tmp/fib-repl -x .sls --r6rs --no-auto-compile`.

## 3. Import, open a session, query

```scheme
(import (ychr) (ychr generated fib))
(define s (open-session fib))
(query s "fib/2" 10 'R)
```

Output:

```
R = 55
```

- `fib` is the **program-info dispatcher** exported by
  `(ychr generated fib)` — a small procedure with two cases:
  `(fib 'init)` builds a fresh session and `(fib 'tells)` returns the
  `"module:name/arity" → tell-procedure` lookup. `open-session` calls
  both for you.
- Arguments that are symbols starting with an uppercase letter or
  `_` (Prolog convention) become fresh logical variables and are
  reported in the printed bindings. Other arguments are passed
  through unchanged.
- To pass an *atom* whose source spelling happens to start with an
  uppercase letter, wrap it as a literal — e.g. the atom value
  itself, `(string->symbol "Foo")`, or any non-symbol carrier. The
  parser is deliberately strict so that the common case
  (`(query s "p/2" 1 'X)`) needs no ceremony.

Run more queries against the same session — for tells whose rule
bodies modify the constraint store, the second query sees the first
query's effects:

```scheme
(query s "fib:fib/2" 5 'R)
(query s "fib/2" 7 'A)
```

```
R = 5
A = 13
```

(fib does not share state across calls, so the two answers are
independent — but `s` is the same store for both.)

## Constraint names: qualified vs short

`query` accepts two forms:

- **Qualified**: `"module:name/arity"` — always works.
- **Short**: `"name/arity"` — works when exactly one constraint in
  the program has that local name and arity.

If two modules export the same `name/arity`, the short form is
ambiguous and `query` reports both candidates so you can disambiguate:

```
Exception in query: ambiguous short name 'bar/2' (candidates: foo:bar/2, baz:bar/2); use the qualified form
```

A name that doesn't resolve:

```scheme
(query s "fib/3" 10 'R 'Q)
```

```
Exception in query: no constraint named fib/3
```

Forgetting `open-session` is the other common slip:

```scheme
(query s "fib/2" 10 'R)
```

```
Exception in query: no program registered; call (open-session prog) first
```

## What `query` can and can't do

`query` dispatches **tell** goals only — constraints declared with
`:- chr_constraint`. The body of a CHR rule (including arithmetic
like `R is N - 1`) runs as usual once the goal fires; this restriction
is only about what you can type at the top level.

For top-level goals that aren't a tell — e.g. evaluating a function
call like `fib(10)` outside any constraint — fall back to either
`ychr gen-driver` (one-shot scripts) or call the generated
`func_module__name_arity` procedure directly from the REPL.

## Multiple programs in one session

If you have two compiled programs loaded and want to query each, use
`with-program` for the scope:

```scheme
(import (ychr) (ychr generated fib) (ychr generated bakery))
(define sf (open-session fib))
(define sb (open-session bakery))   ; open-session also sets the implicit context

(with-program fib
  (query sf "fib/2" 6 'R))
(with-program bakery
  (query sb "cake/0"))
```

`open-session` mutates the implicit current-program parameter, so
when you've called it twice the most recent program is what `query`
defaults to — wrap the older one in `with-program` to switch back.

## See also

- [`docs/reference/cli.md`](../reference/cli.md) — `ychr compile -t scheme` and `ychr gen-driver`.
- [`docs/how-to/use-the-repl.md`](use-the-repl.md) — the Haskell-side
  `ychr repl`, which speaks CHR source directly (no Scheme).
