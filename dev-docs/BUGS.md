# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries below now carry an agreed fix plan with the owner's decisions
already made. A later session can implement straight from the "Fix
sketch", without re-asking what to do. Line numbers are approximate
(the file has moved since).

Remove entries from this file when the underlying bug is fixed.

## 3c. `:- chr_type ','(A, B) ---> ...` declares a type named `,`

**Documented claim.** None stated — `,` is not listed as a reserved
type name anywhere; whatever check rejects other reserved words as
declaration names doesn't cover `,`.

**Test.** (Verified against the built binary.)

    :- module(tc4, [go/1]).
    :- chr_type ','(A, B) ---> foo.
    :- chr_constraint go/1.
    go(R) <=> R = 1.

    ychr check tc4.chr

(Params must be variables — `','(a, b)` with lowercase atoms instead
hits `YCHR-15018 Invalid type parameter` first, which is a correct,
unrelated check. Also note `:- chr_type (a, b) ---> foo.` written
with a space does *not* reproduce this: that parses as the directive
name `chr_type` applied to `(a, b)` as two arguments, i.e. a
different, unknown directive `--->/2`, giving `YCHR-15024`. The
repro needs the quoted-atom functor form `','(A, B)`.)

**Expected.** Rejected — `,` is a control form, not a legal type (or
constructor/atom) name, the same way other reserved symbols are
rejected as declaration names.

**Actual.** Exit 0, no diagnostic at all. The type `,` /2 is declared
successfully with no warning or error.

**Fix sketch.** Not investigated beyond the repro. Reserve `","` as a
type name — add it wherever type-name declarations are validated
(likely alongside other reserved-name checks in `Resolve.hs`/
`Rename.hs`), reported with the existing reserved-name error for that
position rather than a new code. Needs a look at how other reserved
names (`tell`, the aggregate forms) are rejected as *type* names, if
at all, to reuse the same mechanism rather than inventing one just
for `,`.

## A lambda bound with `=` keeps a `quote(...)` wrapper

**Documented claim.** `docs/reference/language.md` §Lambdas: a lambda
is a first-class value. Nothing says it looks different depending on
how it was bound.

**Test.**

    :- chr_constraint k/1, j/1.
    k(F) <=> F = fun(X) -> X + 1 end.
    j(F) <=> F is fun(X) -> X + 1 end.

    ychr run k.chr -g 'k:k(F)' --show-bindings
    ychr run k.chr -g 'k:j(F)' --show-bindings

and, in `ychr repl`, `F = fun(X) -> X + 1 end.`

**Expected.** `F = fun(X) -> prelude:(X + 1) end` in all three.

**Actual.**

    F = quote(fun(X) -> prelude:(X + 1) end)    % k, and the REPL
    F = fun(X) -> prelude:(X + 1) end           % j

The Scheme backend prints the same difference on the raw term:
`'__closure'(k:'__lambda_0', quote(fun('X') -> ...))` for `k`, without
the `quote` for `j`. Calling the closure works either way
(`F = fun(X) -> X + 1 end, R is '$call'(F, 1)` gives `R = 2`). What differs
is the term itself: printing shows it, and so would code that compares
or takes apart two closures.

**Notes.** Lambda lifting (`Desugar.hs`, ~line 782) builds the closure
as `__closure(Id, quote(Source), Captures...)`. The `quote` is there so
`compileExpr` builds `Source` as data (its `quote/1` arm calls
`compileTerm`, `Compile.hs` ~line 1958), and the wrapper itself
disappears. But `=` lowers its operands with `compileTerm .
exprToTerm` (`Compile.hs` ~line 2572), and there `quote/1` is just a
compound, so it stays in the term. That's the spec for a user-written
`quote` under `=`, so the fix can't be "strip `quote` under `=`".

**Fix sketch.** Not decided. One option: drop the `quote` from the
closure, and give `compileExpr` a `__closure` arm that builds the
source slot with `compileTerm`. Then both paths build the same term.
If so, `Desugar/Inline.hs`'s `rewriteExpr` needs a matching
`__closure` arm. It skips `quote` today, and that's the only thing
keeping it from inlining calls in the lambda's printed body
(`inline_basic/lambda_body` pins that). Add a golden with the `k` and `j`
cases above.
