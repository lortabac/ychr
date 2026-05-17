# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

For terse, fix-shaped formatting, see `SCHEME_BACKEND_GAPS.md`. Remove
entries from this file when the underlying bug is fixed.


## Cross-module function-call leak in `Resolve.termToExpr`

**Where:** `src/YCHR/Resolve.hs:934-948` (the `CompoundTerm name@(Unqualified n) args` fallback in `termToExpr`).

**What:** When `termToExpr` encounters an unqualified compound that the
renamer left unqualified (because no visible provider exists in the
current module's scope), it searches the *program-wide* function set
`fs :: Set QualifiedName` for any qualified name with matching local
name. If exactly one match exists, it canonicalizes the compound to a
`CallExpr` and the call happens at runtime — even though the calling
module never imported the declaring module.

The lookup ignores the calling module's import list entirely. This
violates the encapsulation contract that `use_module` is supposed to
provide.

**Affected positions.** The fallback fires anywhere `termToExpr` runs
over an unqualified compound the renamer didn't qualify. In practice:

- *Tell-side constraint args* (rule bodies, top-level goals): renamer
  uses `NoResolve` for body-compound children, so the name reaches
  `termToExpr` unqualified by design. The bug is silent here — no
  rename warning is emitted (see `Rename.hs`'s
  `visibleProviders`-gated suppression in the `NoResolve` compound
  branch).

- *`is` RHS, rule guards, equation guards, equation RHS, lambda
  bodies*: renamer uses `ResolveAll`, which calls `visibleProviders`.
  When that returns empty, the renamer emits an `UnknownName` warning
  and leaves the name unqualified — and `termToExpr`'s fallback then
  matches globally. The warning message ("undeclared data
  constructor") is misleading: it suggests the user typoed a
  constructor name, when in fact the program is silently calling a
  function from an unimported module.

**Repro.**

```
% maths.chr
:- module(maths, [add/2]).
:- function add/2.
add(X, Y) -> X + Y.
```

```
% app.chr
:- module(app, [run/2]).
:- use_module(prelude).         % does NOT use_module(maths)
:- chr_constraint run/2.

run(X, R) <=> R is add(X, 1).
```

Compile both files together and run `app:run(5, R)`. Expected
behaviour: `app` cannot see `add/2` because it didn't import it; the
program should either reject the call at compile time or store
`add(5, 1)` as a literal compound. Actual behaviour: `add(5, 1)`
silently evaluates to `6` via `maths:add`.

Replacing `add` with a name that exists in two loaded modules triggers
the second failure mode: `termToExpr` finds 2+ matches and falls
through to `CtorExpr` (silent degradation to a data term, again with
no diagnostic).

**Why it exists.** `termToExpr`'s signature only takes the
program-wide function-name set:

```haskell
termToExpr ::
  Set QualifiedName ->
  P.SourceLoc -> PExpr.PExpr -> Term ->
  Writer [Diagnostic ResolveError] R.Expr
```

When the canonicalization was added to support tell-side argument
evaluation (`foo(1 + 2)` → `CallExpr prelude:+`), no per-module
visibility view was threaded through. The renamer has the right
information (via `RenameCtx.declEnv` + `currentModule.imports` +
`visibleProviders`), but Resolve does not.

**Fix sketch.** Build a per-module visibility table during
`resolveProgram` and thread it through to `termToExpr`:

1. In `Resolve.resolveProgram`, for each module compute
   `Map (Text, Int) QualifiedName` containing exactly the
   `(localName, arity)` → `qualifiedName` entries for functions
   visible in that module (its own declarations + visible imports).
   The renamer's `visibleProviders` is the reference algorithm.
2. Pass that per-module map into `resolveRules` /
   `resolveFunctions` / `resolveBodyGoals` so each `termToExpr`
   call uses the appropriate module's view.
3. Replace `termToExpr`'s `fs :: Set QualifiedName` parameter with
   the visibility map. The fallback at `Resolve.hs:934-948`
   becomes a single `Map.lookup (n, length args) visibilityMap`:
   `Just qn` → `CallExpr qn`, `Nothing` → `CtorExpr`.
4. Once the fix is in, remove the `visibleProviders`-gated warning
   suppression in `Rename.hs`'s `NoResolve` compound branch — the
   warning becomes meaningful again (it'll only fire when the name
   really is an undeclared data constructor).
5. The two new failure modes (cross-module leak / silent
   ambiguity-degradation) should each get a regression golden under
   `test/golden/`.

**Workaround.** Until fixed: qualify any function call that isn't
unambiguously a prelude operator (`maths:add(X, 1)` instead of
`add(X, 1)`). Qualified compounds go through the existing
visibility-validated path at `Resolve.hs:921-925`.
