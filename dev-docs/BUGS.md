# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries below now carry an agreed fix plan with the owner's decisions
already made. A later session can implement straight from the "Fix
sketch", without re-asking what to do. Line numbers are approximate
(the file has moved since).

Remove entries from this file when the underlying bug is fixed.

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
