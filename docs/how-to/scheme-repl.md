# How to drive a compiled CHR program from a Scheme REPL

The `(ychr)` library bundles the runtime plus `open-session` and
`tell`; a session
is three lines after the imports.

You need a source checkout. Generated Scheme imports the YCHR runtime
in [`scheme/`](../../scheme/), which the Hackage package does not
ship. Compiling from an installed `ychr` works; running the output
needs the checkout on the Scheme library path (step 2).

## 1. Compile

`-n NAME` names the generated library (the identifier you open a
session with); the default is `program`.

```sh
ychr compile -t scheme -n fib -d /tmp/fib-repl test/golden/fib/fib.chr
# → /tmp/fib-repl/ychr/generated/fib.sls
```

## 2. Start the REPL

```sh
scheme --libdirs PROJECT_ROOT/scheme:/tmp/fib-repl --libexts .sls
```

First `--libdirs` entry: the runtime. Second: the compiled program.
`--libexts .sls` makes Chez load R6RS `.sls` files. Guile:
`guile3.0 -L PROJECT_ROOT/scheme -L /tmp/fib-repl -x .sls --r6rs --no-auto-compile`.

## 3. Import, open a session, tell

```scheme
(import (ychr) (ychr generated fib))
(define s (open-session fib))
(tell s fib:fib/2 10 'R)
```

Output:

```
R = 55
```

- `fib` is the session thunk; `open-session` calls it and gets a fresh
  store. Sessions share nothing.
- `fib:fib/2` is the tell-procedure alias for constraint `fib:fib/2`,
  resolved at expand time — no per-call lookup.
- A symbol starting with an uppercase letter or `_` is a logical
  variable. The same symbol twice in one call is one variable; a bare
  `_` is fresh each time. Uppercase ones are printed, `_`-prefixed
  ones are not. Anything else passes through as an atom.
- Two query variables that end up unified but still unbound print as
  each other (`A = B`, `B = A`), the same as `ychr run --show-bindings`.
- `(string->symbol "Foo")` is still `'Foo`, so it's still a variable.
  For a capitalized atom, skip `tell` and call the alias directly:
  `(fib:fib/2 s 10 r)` with `r` from `make-var`. There a symbol is
  always an atom.

`s` is one store across tells. (`fib` does not depend on prior state,
so these two answers are independent.)

```scheme
(tell s fib/2 5 'R)
(tell s fib:fib/2 7 'A)
```

```
R = 5
A = 13
```

## Aliases: qualified vs short

Per exported constraint the library exports `module:name/arity`
(always) and `name/arity` (only when no other exported constraint in
the library has that `name/arity`; otherwise reach both as
`mod1:foo/2` / `mod2:foo/2`).

An unknown name is an expand-time error — raised when the library
loads, not when `tell` runs. Wording varies by implementation:

```scheme
(tell s nonexistent/3 10 'R 'Q)
```

```
ERROR: In procedure %resolve-variable:
Unbound variable: nonexistent/3
```

## What `tell` does

`tell` posts one declared constraint. Rule bodies run as usual; the
restriction is on what you type at top level. For any other goal
(`fib(10)` outside a constraint, say) call the generated
`func_<module>__<name><arity>` procedure (e.g. `func_fib__fib1`)
directly, or use `ychr gen-driver`,
which writes a one-shot driver to stdout:

```sh
ychr compile -t scheme -d build/ examples/bakery.chr
ychr gen-driver -g cake examples/bakery.chr > build/run.scm
```

The goal may not contain a lambda (`YCHR-50004`); pass `fun name/arity`.

## Lists

A CHR list is a plain Scheme list, so you can pass one in and use one
that comes out. Take this program, saved as `/tmp/lst.chr`:

```prolog
:- module(lst, [total/2, upto/2]).
:- use_module(library(lists)).
:- chr_constraint total/2, upto/2.

total(L, R) <=> R is sum_list(L).
upto(N, L) <=> L is range(1, N).
```

Compile it with `-n lst`, then:

```scheme
(import (ychr) (ychr generated lst))
(define s (open-session lst))
(tell s total/2 '(1 2 3) 'R)
```

```
R = 6
```

A list that comes back may still go through bound logical variables
(here `l` itself). `deep-deref` follows them all and gives a plain list:

```scheme
(define l (make-var s))
(begin (upto/2 s 4 l) (deep-deref l))
(apply + (deep-deref l))
```

```
(1 2 3 4)
10
```

Notes:

- The empty list `[]` is `'()`. It is still an atom to CHR
  (`atom([])` is true); `chr-atom?` is the runtime's test.
- `tell` only turns *top-level* uppercase symbols into variables. In
  `'(A B)` the `A` and `B` are atoms.
- Elements are CHR values: atoms are symbols, but a qualified one is
  mangled (`mod:foo` is `mod__foo`), and other compounds are opaque
  records (`term?`, `term-functor`, `term-args`).

## Multiple programs in one session

```scheme
(import (ychr) (ychr generated fib) (ychr generated bakery))
(define sf (open-session fib))
(define sb (open-session bakery))
(tell sf fib:fib/2 6 'R)
(tell sb bakery:cake/0)
```

Short aliases are generated per library, so two libraries can export
the same one; the import then refuses to load. Take only the qualified
forms with `(only ...)`, or `(rename ...)`:

```scheme
(import (ychr)
        (only (ychr generated fib)    fib    fib:fib/2)
        (only (ychr generated bakery) bakery bakery:cake/0))
```

## See also

- [REPL reference](../reference/repl.md) — `ychr repl` takes CHR
  source directly, no Scheme. Its `--repl-backend=chez` option runs
  queries in a Chez process for you, instead of the manual `(ychr)`
  session described above.
