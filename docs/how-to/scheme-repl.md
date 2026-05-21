# How to drive a compiled CHR program from a Scheme REPL

> **Goal:** compile a CHR program once with `ychr compile -t scheme`,
> then poke at it interactively from Chez (or Guile) without
> hand-writing a driver script.

The umbrella `(ychr)` library bundles the runtime plus the helpers
`open-session` and `tell`, so a typical session is three user lines
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

## 3. Import, open a session, tell a constraint

```scheme
(import (ychr) (ychr generated fib))
(define s (open-session fib))
(tell s fib:fib/2 10 'R)
```

Output:

```
R = 55
```

- `fib` is a **session thunk** exported by `(ychr generated fib)` —
  invoking it (which is what `open-session` does) returns a fresh
  store. Open as many sessions as you like; they don't share state.
- `fib:fib/2` is the **tell-procedure alias** for the constraint
  `fib:fib/2`. The generated library exports one such identifier per
  exported constraint, so the Scheme compiler resolves the call at
  expand time — there is no per-call name lookup.
- Arguments that are symbols starting with an uppercase letter or
  `_` (Prolog convention) become fresh logical variables and are
  reported in the printed bindings. Other arguments are passed
  through unchanged.
- To pass an *atom* whose source spelling happens to start with an
  uppercase letter, wrap it as a literal — e.g. the atom value
  itself, `(string->symbol "Foo")`, or any non-symbol carrier. The
  parser is deliberately strict so that the common case
  (`(tell s p/2 1 'X)`) needs no ceremony.

Run more tells against the same session — for constraints whose rule
bodies modify the store, later calls see earlier calls' effects:

```scheme
(tell s fib/2 5 'R)
(tell s fib:fib/2 7 'A)
```

```
R = 5
A = 13
```

(fib does not share state across calls, so the two answers are
independent — but `s` is the same store for both.)

## Constraint aliases: qualified vs short

The generated library exports two identifiers per exported constraint:

- **Qualified**: `module:name/arity` (e.g. `fib:fib/2`) — always
  emitted.
- **Short**: `name/arity` (e.g. `fib/2`) — emitted when no other
  exported constraint in the same library has the same `name/arity`.

If two modules in one compilation unit share a short name, only the
qualified aliases are emitted for those constraints; reach them as
`mod1:foo/2` and `mod2:foo/2`.

A name that doesn't resolve raises an R6RS expand-time error:

```scheme
(tell s nonexistent/3 10 'R 'Q)
```

```
ERROR: In procedure %resolve-variable:
Unbound variable: nonexistent/3
```

(Wording varies by Scheme implementation. The key point: the error
fires at expand time, not at the moment of the `tell` call — the
identifier is checked the moment the library is loaded.)

## What `tell` can and can't do

`tell` dispatches **tell** goals only — constraints declared with
`:- chr_constraint`. The body of a CHR rule (including arithmetic
like `R is N - 1`) runs as usual once the goal fires; this restriction
is only about what you can type at the top level.

For top-level goals that aren't a tell — e.g. evaluating a function
call like `fib(10)` outside any constraint — fall back to either
`ychr gen-driver` (one-shot scripts) or call the generated
`func_module__name_arity` procedure directly from the REPL.

## Multiple programs in one session

Importing two libraries side by side just works as long as their
short aliases don't collide:

```scheme
(import (ychr) (ychr generated fib) (ychr generated bakery))
(define sf (open-session fib))
(define sb (open-session bakery))
(tell sf fib:fib/2 6 'R)
(tell sb bakery:cake/0)
```

If both libraries happen to emit the same short alias (each library
produces short aliases independently, so cross-library collisions are
not detected at compile time), the importing R6RS module will refuse
to load. Use `(only ...)` to take only the qualified form, or
`(rename ...)` to disambiguate:

```scheme
(import (ychr)
        (only (ychr generated fib)    fib    fib:fib/2)
        (only (ychr generated bakery) bakery bakery:cake/0))
```

Either form keeps each program addressable from the same session
without giving up the alias-based static dispatch.

## See also

- [`docs/reference/cli.md`](../reference/cli.md) — `ychr compile -t scheme` and `ychr gen-driver`.
- [`docs/how-to/use-the-repl.md`](use-the-repl.md) — the Haskell-side
  `ychr repl`, which speaks CHR source directly (no Scheme).
