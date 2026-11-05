# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries below now carry an agreed fix plan with the owner's decisions
already made. A later session can implement straight from the "Fix
sketch", without re-asking what to do. Line numbers are approximate
(the file has moved since).

Remove entries from this file when the underlying bug is fixed.

## An unparenthesized multi-bound `requiring` clause silently keeps only the first bound

**Documented claim.** type-system.md §Declaration syntax: the
`requiring` clause is a comma-separated list of bound signatures. Its
`clamp` example now puts each bound in parens; written bare it breaks:

    :- function clamp(T, T, T) -> T requiring
        '>'(T, T) -> bool,
        '<'(T, T) -> bool.

**Test.** Give this `clamp` a body and a goal that calls it, then
`ychr check`.

**Actual.** `:info clamp:clamp` shows the clause back almost verbatim:

    :- function clamp(T, T, T) -> T requiring prelude:'>'(T, T) -> bool, T < T -> bool.

but there is only one `BoundSig`, for `>`, whose return type is the
junk compound `->(,(bool, <(T, T)), bool)` — the `<` bound is
swallowed. `clamp`'s own body then fails to type-check:

    Type mismatch: '->(,(prelude:bool, <(T#20, T#20)), prelude:bool)' does not match 'prelude:bool'

**Notes.** `,` (1000) binds tighter than `->` (1110), so `r1, b2 ->
r2` parses as `->(','(r1, b2), r2)` inside the first bound.
`convertBoundSig` (`Parser.hs`) accepts any compound as a return type.
The comment above `requiring` in `builtinOps` says the list is a
clean comma chain; that only holds when each bound is parenthesized.
This is the same `requiring`-list grammar used by `:- function`/
`:- open_function`/`:- class`/`:- open_class`/`:- extend_class_type`.

**Fix sketch.** Owner decision: reject a bare `,` or `->` inside a
type (outside a `fun(...) -> T end` function type) with a new error,
`YCHR-15030` (`CommaOrArrowInType`). Second commit, after the DSL fix
above.

1. `Parser.hs`'s `convertTypeExpr`, before the generic `Compound`
   arm: a `Compound "->" [Compound "fun" args, ret]` keeps today's
   output (recursively); any other `Compound "->" _` or `Compound ","
   _` becomes `Left (CommaOrArrowInType ...)`.
2. `ParseValidationError`: add nullary `CommaOrArrowInType`.
3. `Display.hs`: code 15030; message "',' or '->' inside a type";
   hint: "a function type is `fun(T1, ..., Tn) -> T end`; to list
   several signatures, parenthesize each: `(f(T) -> T), (g(T) -> T)`".
4. Fix the stale `builtinOps` comment near `requiring` (~line
   123-125) to explain why an unparenthesized multi-bound list is
   now rejected rather than silently mis-parsed.
5. `Resolve.hs`'s `isFunctionType` comment (~1184): note the parser
   never produces a nested non-function `->` type any more (only the
   DSL still can, since the DSL builds `TypeExpr` directly).
6. Tests: `ParserTest` cases for bare two-bound `requiring` on
   `:- function` and `:- chr_constraint` (rejected with
   `CommaOrArrowInType`); still accepted: parenthesized multi-bound,
   and a bound returning `fun(T) -> T end`. New golden
   `unparenthesized_signatures/` with several `.error` cases (bare
   `clamp`, `class`, `extend_class_type`, `chr_constraint`).
7. Docs: `type-system.md` §Bounded Polymorphism and §Signature
   Overloading declaration syntax — note multiple bounds must each be
   parenthesized, and a bare `,`/`->` is `YCHR-15030`.
8. CHANGELOG + breaking-change bullet (new error constructor).
9. Remove this entry from BUGS.md.

## 3a. A qualified data constructor at the wrong arity reports "module does not export" instead of an arity error

**Documented claim.** `docs/reference/type-system.md` §Known
constructors: using a declared constructor at the wrong arity is a
type error (`ConstructorArityMismatch`, `YCHR-60008`); data
constructors are name-only in the type system (any arity of a name
is "the same constructor" for ambiguity purposes; the unqualified
path already resolves name-only).

**Test.**

    % a.chr
    :- module(a, [type(ta/0)]).
    :- chr_type ta ---> foo(int).

    % c.chr
    :- module(c, [go/1]).
    :- use_module(a).
    :- chr_constraint go/1.
    go(R) <=> R = a:foo(1, 2).

    ychr check a.chr c.chr

**Expected.** A constructor-arity error (`YCHR-60008`, or the
`YCHR-20102` renamer warning), the same as the unqualified case,
since `foo` is declared (at arity 1) and the problem is purely arity.

**Actual.**

    === error ===
    c.chr:5:11: YCHR-20009
    Module 'a' does not export 'foo/2'

Exit code 1, and no YCHR-60008/20102. (Verified against the built
binary in the worktree.)

**Notes.** This case was left open on purpose when the unqualified
path moved to name-only resolution. Qualified lookup (`validateQualified` and friends) is keyed on
`(name, arity)` as a pair, so a qualified reference at the wrong
arity looks like a reference to a name that just isn't exported,
rather than "exported, but at a different arity". Since data
constructors are name-only, this is arguably the same bug as the
unqualified one, just on the qualified path.

**Fix sketch.** Not decided yet. When picked up: give qualified data
constructor lookup the same name-only treatment as the unqualified
path now has — check the module exports the *name* at any
arity, and if so, report an arity mismatch instead of "not exported".
Needs its own `(module, name)`-keyed (not `(module, name, arity)`)
visibility check for data constructors specifically; function/
constraint qualified lookup should stay arity-keyed, since those
*are* overloaded by arity in a sense functions are not (actually:
functions and constraints are also name+arity keyed for real
collisions — only data constructors are name-only). Compare with
`test/golden/typecheck_constructor_arity_imported`, the unqualified
case.

## 3b. A data constructor named `'?'/1` is accepted but every use is rejected

**Documented claim.** None stated — `?/1` is not listed as reserved
for data constructors anywhere in the docs.

**Test.**

    :- chr_type t ---> '?'(int).
    :- chr_constraint go/1.
    go(R) <=> R = '?'(1).

    ychr check t.chr

**Expected.** Either: accepted and usable like any other constructor,
or rejected at declaration time with a clear "reserved" error.

**Actual.** The `:- chr_type` declaration itself is accepted. Every
*use* of `'?'(1)` — including in plain data position, inside `quote`,
anywhere — is rejected with `YCHR-20042`
(`GuardOutsideAggregateGoal`), the same error a bare guard-form `?/1`
gets. `isGuardFunctor` (Rename.hs ~1541-1542) matches on name `"?"`
and arity 1 unconditionally, with no check for whether a visible data
constructor of that name/arity actually exists — it fires in data and
quoted positions too, where the guard-form interpretation doesn't
even apply. (Verified against the built binary: declaration succeeds,
`check` on the use fails with 20042, exit 1.)

**Fix sketch.** Owner to decide between two options (record both,
pick later):

- (a) Reject the *declaration* instead: `'?'/1` as a data constructor
  name is reserved, the same way the aggregate keys are reserved for
  constraints/functions/macros. Simple, consistent with "`?` is
  reserved for aggregates" (`?/1` is already reserved for
  constraints, functions and goal macros, YCHR-20043), but makes
  `?` unavailable as a constructor name forever.
- (b) Let data/quoted positions win: `isGuardFunctor`'s callers already
  know whether they're in a position where the guard-form
  interpretation even applies (data argument, pattern, `quote(...)`);
  only treat `'?'(X)` as the guard form when no visible constructor
  named `?/1` exists, and as plain data otherwise. More permissive,
  but adds a visibility lookup to a hot path and a "which one wins"
  rule to document.

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
