# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

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
