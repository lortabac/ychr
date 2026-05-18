# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

For terse, fix-shaped formatting, see `SCHEME_BACKEND_GAPS.md`. Remove
entries from this file when the underlying bug is fixed.

## Underscore-prefixed variables (`_X`, `_Tail`) are rejected by the parser

`docs/reference/syntax.md:28` states: "Variables start with an
uppercase letter or underscore, then letters, digits, or underscores.
The bare `_` is the wildcard." The expressions table at
`docs/reference/syntax.md:130` lists `_Tail` as an example. Only the
bare `_` is accepted today; any `_<id>` form is a parse error.

Repro:

```chr
:- module(q).
:- chr_constraint p/1.
p(_X) <=> true.
```

Actual: `YCHR-50001 unexpected 'X'`. Fails uniformly in head patterns,
body arguments, `term(...)` bodies, list tails (`[H | _Tail]`), and
CLI goals (`-g 'q:p(_X)'`).

## Declared-but-unreferenced constraints crash at goal time with a raw `user error`

A constraint declared with `:- chr_constraint c/n.` but never
mentioned in any rule cannot be told: the runtime fails with
`Error: user error (Constraint not found: tell_M__cn)`, not a
YCHR-NNNNN diagnostic. Adding any rule that mentions `c/n` (even
`c(_) ==> true.`) is enough to make it tellable, so the compiler
appears to emit `tell_c` only for constraints reached from rule sites.

Repro:

```chr
:- module(rt, [p/1]).
:- chr_constraint p/1.
```

Goal: `rt:p(1)`. Expected: silent success (no rule fires, constraint
stored). Actual: `user error (Constraint not found: tell_rt__p1)`,
exit 1.

## `=` in body cannot introduce a fresh variable (asymmetric with `is`)

`docs/reference/language.md` §Tell-side evaluation lists "the
right-hand side of `is` and `=`" symmetrically as evaluating positions.
In practice `Y = 10, R = Y` in a body is rejected as unbound while
`Y is 10, R = Y` is accepted. The error hint ("variables used in a
guard or body must also appear in the rule head") is also wrong —
`is`-introduced variables don't appear in the head either.

Repro:

```chr
:- module(q).
:- chr_constraint test/1.
test(R) <=> Y = 10, R = Y.
```

Goal: `q:test(R)`. Actual: `YCHR-40002 Unbound variable 'Y'`. The
asymmetry between `is` and `=` for body-introduced variables is not
documented anywhere.

## `term(...)` quoting produces spurious YCHR-20101 warnings

`docs/reference/language.md` §The `term/1` quoting form documents
`term` as a reserved keyword and the quoted body as a "surface term"
(opaque data, not subject to constructor-undeclared checks). Today
both `term` itself and any non-declared functor inside the quoting
form trigger `YCHR-20101 Undeclared data constructor ...`, which
turns into hard `--Werror` failures on any program that uses
`term(...)`.

Repro:

```chr
:- module(q).
:- chr_constraint store/1, ask/1, go/2.
store(X), ask(R) <=> R = X.
go(X, R) <=> store(term(plus(X, 3))), ask(R).
```

Output includes:

```
YCHR-20101 Undeclared data constructor 'plus'
YCHR-20101 Undeclared data constructor 'term'
```

The resolver should treat `term/1` as the wired-in quoting form (the
same special case that underwrites YCHR-16003) and should not walk
into a `term(...)` body looking for constructor declarations.

## `=` in guard position type-checks but crashes at runtime

`dev-docs/PROJECT.md` ("Guards use `Equal`, bodies use `Unify`") and
`docs/reference/type-system.md` §8 (guard term type must be consistent
with `prelude:bool`) jointly imply that `=` in guard position is a
static error. The check passes silently today; the program crashes
at goal time with `YCHR-60001 BFromVal: expected boolean`, with no
hint that the user wrote `=` where `==` was expected. The same hole
exists for any host function with `any` return type used in guard
position.

Repro:

```chr
:- module(q).
:- chr_constraint test/2.
test(X, R) <=> X = 5 | R = 1.
test(_, R) <=> R = 0.
```

Goal: `q:test(5, R)`. Expected: static rejection at `ychr check`.
Actual: silent compile + runtime crash.

## Prelude advertises `rem/2` but the host has no implementation

`docs/reference/prelude.md` §Arithmetic lists `rem/2` (priority 400,
yfx in the operator table). The prelude desugars `X rem Y` to
`host:'rem'(X, Y)` (`libraries/prelude.chr:122`), but the Haskell
runtime registers no `rem` host call.

Repro:

```chr
:- module(q).
:- chr_constraint test/1.
test(R) <=> R is 10 rem 3.
```

Actual: `YCHR-60001 invokeHostCall: unknown host call rem`. Fix
sketch: register `rem` alongside `div` and `mod` in the host-call
table (`src/YCHR/Runtime/Registry.hs` or wherever the arithmetic
primitives live).

## Zero-parameter lambda `fun() -> Body end` silently degrades to a compound term

`docs/reference/syntax.md` §Expressions and `docs/reference/language.md`
§Lambdas say lambda parameters are "restricted to variables and
wildcards" but do not forbid an empty parameter list. Today the parser
silently re-interprets `fun() -> Body end` as the compound term
`'->'(fun(), Body)`, then the resolver emits `YCHR-20101` warnings
for both `fun` and `->`. The user ends up with a piece of data, not a
callable thunk: `'$call'(F)` on it returns the unevaluated compound
rather than `Body`.

Repro:

```chr
:- module(q).
:- chr_constraint test/1.
test(R) <=> R = fun() -> 42 end.
```

Expected: either a clean parse-time rejection ("lambdas require at
least one parameter") or a working thunk callable via `'$call'(F)`.
Actual: degraded to compound + warnings; `R = fun() -> 42 end`.

## Qualified access bypasses the exporter's constructor allowlist

`docs/reference/language.md` §Type and constructor exports promises
that a constructor not in the type's export allowlist is invisible to
importers (the "only `red`" example, YCHR-20008 on violations).
Qualified syntax `palette:green` reaches in and uses a non-exported
constructor anyway. A second sub-finding: when an *import* list
mentions a non-exported (but declared) constructor, the diagnostic
says "constructor `green` is not declared on the type," which is
wrong — it *is* declared, just not exported.

Repro:

```
palette.chr:
    :- module(palette, [type(col/0, [red])]).
    :- chr_type col ---> red ; green ; blue.

user.chr:
    :- module(user).
    :- use_module(palette).
    :- chr_constraint test/1.
    test(R) <=> R = palette:green.
```

Goal: `user:test(R)`. Actual: `R = palette:green()`, exit 0.
Expected: rejection of the qualified reference (the allowlist should
apply to qualified syntax too). Suspect site: constructor resolution
in `src/YCHR/Resolve.hs` does not consult the per-type export
allowlist when the reference is fully qualified.

## `bound_cycle` diagnostic duplicates the last vertex

`docs/reference/type-system.md` §Errors documents `bound_cycle` as a
cycle in the bound graph: "a function that requires itself directly,
or any longer chain of `requiring`-clause edges that returns to its
starting function." Today the printed path duplicates the final
vertex rather than wrapping back to the start.

Repro:

```chr
:- module(q).
:- function foo(T) -> T requiring bar(T) -> T.
:- function bar(T) -> T requiring foo(T) -> T.
foo(X) -> X.
bar(X) -> X.
```

Actual: `YCHR-16010 Cyclic 'requiring' clause: q:foo -> q:bar -> q:bar`.
Expected: `... q:foo -> q:bar -> q:foo` (the cycle closes on its
starting vertex).

## `unknown_bound_function` is reported as the generic YCHR-20002

`docs/reference/type-system.md` §Errors lists
`unknown_bound_function` as a distinct error class: "a `requiring`
clause references a function that has not been declared." Today the
renamer emits the generic `YCHR-20002 Unknown name 'nonexistent/1'`
with the standard hint about `:- chr_constraint` / `:- function` /
imports — no indication that the unknown name lives in a `requiring`
clause. Compare to `unbound_bound_variable` (YCHR-16008), which does
get its own code.

Repro:

```chr
:- module(q).
:- function foo(T) -> T requiring nonexistent(T) -> T.
foo(X) -> X.
```

Actual: `YCHR-20002 Unknown name 'nonexistent/1'`. Expected: a
distinct 16xxx code naming the `requiring` clause, parallel to
YCHR-16008.
