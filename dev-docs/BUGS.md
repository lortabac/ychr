# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

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
