# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries below now carry an agreed fix plan with the owner's decisions
already made. A later session can implement straight from the "Fix
sketch", without re-asking what to do. Line numbers are approximate
(the file has moved since).

Remove entries from this file when the underlying bug is fixed.

## `fun m:name/arity` is always rejected as "does not export `name/0`"

**Documented claim.** `docs/reference/language.md` §Scheme backend
portability: "a qualified `module:name` — which the string reader
accepts but a source `fun` does not — picks one exactly". So a source
`fun m:name/arity` is unsupported, but the error should say so.

**Test.**

    :- module(implib, [gt/2]).
    :- function gt(int, int) -> bool.
    gt(X, Y) -> X > Y.

    :- module(funuser, [bar/2]).
    :- use_module(implib).
    :- chr_constraint bar(int, int).
    bar(X, Y) <=> '$call'(fun implib:gt/2, X, Y) | true.

    ychr check implib.chr funuser.chr

**Expected.** Either accepted (`implib` is imported in full and
exports `gt/2`), or an error that says a qualified `fun` reference is
not supported.

**Actual.**

    === error ===
    funuser.chr:4:15: YCHR-20009
    Module 'implib' does not export 'gt/0'

The term parses as `fun((implib:gt)/2)`. `renameTerm`'s two `fun`
arms (`src/YCHR/Internal/Rename.hs`) only match
`CompoundTerm (Unqualified fname) []` under the `/`, so the qualified
name falls through to the generic case and is checked as `gt/0`.
PROJECT.md already notes the same miss for a query
(`fun prelude:max/2`).

**Fix sketch.** Owner decision: support it, both in source and in
queries.

- Add one `renameTerm` arm for `fun` that handles both the qualified
  and unqualified case via a shared `renameFunRef` helper. It calls
  `resolveName` with `ResolveTop` (same resolution a qualified name
  gets anywhere else) and reuses the existing `validateQualified`
  diagnostics (unknown module, not exported, etc.) — no new
  diagnostics for the "name doesn't exist" cases.
- New error: `FunRefNotFunction` — a `fun` reference (qualified or
  not) that resolves to something that isn't a function (a
  constraint, a data constructor, or `host:...`). Needs a fresh
  rename error code (next free `200xx`; 20045 is free as of this
  writing, but check again — another entry in this file may claim it
  first).
- New goldens: `funref_qualified` (positive: the repro above, made to
  pass) and `funref_not_function` (negative: `fun` pointing at a
  constraint or a data constructor).
- Docs: update `language.md` §Lambdas and function references and
  §Scheme backend portability (the "picks one exactly" sentence is
  now stale). Remove the stale query-side gap sentences in
  `PROJECT.md`'s "Keyed `'$call'` dispatch" entry.

## `?/1` can be declared, then is silently ignored

**Documented claim.** `docs/reference/macros.md` §Heads and
§Diagnostics list the reserved symbols a macro head may not use
(`,`, `;`, …, `tell`, `$compound`, `$atom`). `?` is not in the list.

**Test.**

    :- chr_constraint '?'/1.
    :- macro '?'(X) ---> [go].

**Expected.** Rejected, like the aggregate keys.

**Actual.** Both are accepted with no warning, but every use — head,
body, or through the macro — reports `YCHR-20042` regardless, so the
declaration is dead weight.

**Fix sketch.** Owner decision: reserve `?/1` the same way the
aggregate keys are, under the existing `YCHR-20043`
(`ReservedAggregateName`) — no new code.

- `src/YCHR/Internal/Rename.hs`: add
  `isReservedAggregateKey n a = isAggregateFormKey n a || isGuardFunctor (Unqualified n) a`
  and use it everywhere `isAggregateFormKey` alone currently gates a
  reservation check (the `ReservedAggregateName` call sites, ~1196 and
  ~1208; `isGuardFunctor` already lives at ~1541-1542, pinned to
  `"?"`/arity 1).
- Generalize the `YCHR-20043` message text from naming the aggregate
  forms to something like "reserved for aggregates" (covers `?` too
  without listing it by name).
- `?` stays legal at other arities, and stays legal as a declaration-macro
  head (`:- macro_decls` isn't a goal position, so it's unaffected).
- Data constructor `'?'/1` is a separate, already-listed entry below
  (3b) — don't fold it into this fix.

## `:- inline` rewrites the operands of `=`

**Documented claim.** `dev-docs/PROJECT.md` §Frontend: `=` is pure
structural unification, neither operand evaluated, so `X = 1 + 1`
binds `X` to the symbolic `prelude:+(1, 1)`. The same policy applies
in rule bodies and queries.

**Test.**

    :- chr_constraint h/1.
    h(R) <=> R = 1 + 2.

    ychr run -g 'h(R)' --show-bindings

and, in `ychr repl`, `X = 1 + 2.`

**Expected.** `R = prelude:(1 + 2)` in both.

**Actual.** The rule gives `R = host:(1 + 2)`; the REPL gives
`X = prelude:(1 + 2)`. A non-inlined prelude function is fine:
`R = max(1, 2)` gives `R = prelude:max(1, 2)`.

**Notes.** `Desugar.Inline.rewriteExpr` is applied to both operands
of `D.BodyUnify` (`src/YCHR/Internal/Desugar/Inline.hs`, the
`BodyUnify` arm), so the call to the inlined `+` is replaced by its
body, the `host:+` call. The `=` operand is data, not a call.

**Fix sketch.** Owner decision: do NOT fix this session. Leave as is.
When picked up: don't apply `rewriteExpr` to the `D.BodyUnify`
operands.

## NaN and Infinity print with a bogus `.0` suffix

**Documented claim.** None stated.

**Test.**

    :- chr_constraint go/1.
    go(R) <=> R is 0.0 / 0.0.

    ychr run -g 'go(R)' --show-bindings

and the same with `R is 1.0 / 0.0` and `R is -1.0 / 0.0`.

**Actual.**

    R = NaN.0
    R = Infinity.0
    R = (-Infinity.0)

**Notes.** `show` on a finite `Double` always has a `.` in it (both
GHC and MicroHs), so the `.0`-if-no-dot fallback in `prettyPrec`'s
`showFloat` helper (`src/YCHR/Internal/PExpr.hs`, ~line 750-756) only
ever misfires on NaN/Infinity, where `show` gives `NaN`/`Infinity`/
`-Infinity` with no dot. `SExpr.printSExpr`'s `SFloat` case
(`src/YCHR/Internal/SExpr.hs`, ~line 63-65) has the identical bug;
unreachable today (no source literal spells NaN/Infinity and the
compiler never constant-folds a division) but latent — it feeds VM
serialization (`VM/SExpr.hs` ~390), Scheme literals
(`Backend/Scheme.hs` ~1091), and the driver (`SchemeDriver.hs`
~116, 201). Scheme's own pretty-printer (`scheme/ychr/pretty.sls`)
already prints `+nan.0`/`+inf.0` correctly via the host's
`number->string`.

**Fix sketch.** Owner decisions: use Scheme's spelling on both
backends (`+nan.0`, `+inf.0`, `-inf.0`, printed parenthesized when
negative: `(-inf.0)`); `-0.0` is unchanged (already correct, pin with
a golden); do NOT add a `float_to_int` fix (owner declined, out of
scope); no need to make `read_term_from_string` read these back (it
already doesn't round-trip `1.0e10` either).

1. `SExpr.hs`: export a shared `showFloat :: Double -> String`
   (`isNaN -> "+nan.0"`, `isInfinite -> "+inf.0"/"-inf.0"` by sign,
   else plain `show`). `printSExpr (SFloat n)` uses it. The s-expr
   *parser* needs a matching change to read `+nan.0`/`+inf.0`/
   `-inf.0` back (don't add `+` to `isAtomChar`; add a dedicated
   `pSpecialFloat` alternative tried before the generic atom/int
   parser). No `vmVersion` bump needed.
2. `PExpr.hs`: import `showFloat` from `SExpr` instead of keeping a
   local copy; keep the existing "parenthesize when negative" logic
   around it (NaN is never negative; `-inf.0` gets parens).
3. No Scheme-side change — it's already correct.
4. Tests: new golden `test/golden/float_special/` covering NaN, +inf,
   -inf, -0.0, a nested term holding two of them, and
   `write_term_to_string` of NaN (expect `"+nan.0"` as a string).
   Unit tests: `PrettyTest` (NaN/+inf/-inf render correctly),
   `VM/SExprTest` (round-trip `FloatLit` for +inf/-inf through the
   s-expr format; `-0.0` round-trips via `isNegativeZero`, since `Eq`
   on `Double` fails for NaN so don't add NaN to the generic
   round-trip generator).
5. Docs: `docs/reference/vm.md` (float production), `language.md`
   (~line 1118, "Flonums are the one rendering exception" paragraph —
   add the NaN/Infinity spelling and note they have no source syntax
   and don't read back, same as exponent forms).
6. CHANGELOG entry (one line, see plan for exact wording).
7. Remove this entry from BUGS.md.

## The arity checker misses a wrong-arity use when a constructor name has several arities

**Documented claim.** `docs/reference/type-system.md` §Known
constructors: using a declared constructor at the wrong arity is a
type error (`ConstructorArityMismatch`, YCHR-60008), and the renamer's
own `YCHR-20102` warning reports the same mistake independently.

**Test.**

    % a.chr
    :- module(a, [type(ta/0)]).
    :- chr_type ta ---> foo(int).

    % b.chr
    :- module(b, [type(tb/0)]).
    :- chr_type tb ---> foo(int, int, int).

    % c.chr
    :- module(c, [go/1]).
    :- use_module(a).
    :- use_module(b).
    :- chr_constraint go/1.
    go(R) <=> R = foo(1, 2).

    ychr check a.chr b.chr c.chr

**Expected.** `foo` is declared at arity 1 (module `a`) and arity 3
(module `b`); `foo(1, 2)` matches neither, so the checker should report
`YCHR-60008` the same way it does when `foo` has only one declared
arity.

**Actual.**

    === warning ===
    c.chr:5:11: YCHR-20102
    Data constructor 'foo' used with 2 argument(s) but declared with 1 or 3
    R = foo(1, 2)

Exit code 0. No `YCHR-60008` at all — the checker does not flag the
mismatch when the name resolves to more than one visible arity, even
though it does for the single-arity case
(`test/golden/typecheck_constructor_arity`).

**Notes.** `Rename.canonicalizeDataCon` qualifies a bare constructor
only on an exact `(name, arity)` match, so `foo(1, 2)` reaches the
checker as bare `foo`. The checker's alias table (`typechecker/env.chr`,
`build_con_alias`) is keyed on the name alone and drops any name
declared twice, so `canonicalize_con` leaves it bare, `lookup_con`
misses, and `arity_use_of` takes its `nothing` case, as for an
undeclared name. The renamer keys on `(name, arity)`, so it still sees
`foo/1` and `foo/3`.

**Fix sketch.** Owner decisions: R1 — move to name-only resolution in
the renamer itself (data constructors are name-only in the type
system; see memory note). D2 — remove the checker's and the
exhaustiveness checker's alias tables in the *same* change (they
exist only to patch around the renamer's arity-keyed canonicalization;
once that's gone they're dead weight). D3 — the qualified case
(`a:foo(1, 2)`, wrong arity but written qualified) stays `YCHR-20009`
for now; tracked separately as entry 3a below.

1. **`Rename.hs`**: `canonicalizeDataCon` drops its arity argument;
   resolves `Just (Qualified m n)` when exactly one module exports
   `n` at *any* arity (a new visibility-filtered, nub'd helper,
   `conProvidersAnyArity`, ~line 668). `canonicalizeData` and
   `checkAmbiguousDataCon` lose their arity argument too, and fire
   `AmbiguousDataConstructor` (already `YCHR-20012` — no new code)
   whenever `conProvidersAnyArity` has 2+ entries, not just on an
   exact-arity clash. Update the ~6 call sites and the Haddocks that
   describe the old arity-keyed behavior. Keep `validateQualified`,
   `selfDeclaresAndExports`, `isVisibleDataConAt`,
   `warnUnknownDataCon` as is (`YCHR-20102` still fires for the
   genuinely-wrong-arity case). The repro above becomes
   `c.chr:5:11 YCHR-20012 Ambiguous data constructor 'foo' —
   exported by: a, b` (a different diagnostic, not a silent miss —
   that's fine, it's still a loud error).
2. **Remove the alias tables**: `typechecker/env.chr`
   (`con_env_from`'s alias half, `build_con_alias`, `unique_bases`,
   `based_names`, `based_name`, `count_base`, `canonicalize_con`),
   `typechecker/pure.chr` (`check_arity` goes straight through
   `arity_use_of`; drop `check_canonical`), `skel.chr`/`walk.chr` (a
   couple of call sites pass the constructor name straight through
   now instead of canonicalizing first). `src/YCHR/Internal/
   Constructors.hs` loses `aliases`/`buildConAlias`/`canonicalizeCon`.
   `Exhaustiveness.hs` looks up the con env directly. Watch for:
   compiler-generated bare prelude constructor terms (lists, `true`)
   reaching the checker un-qualified — verify with `make test`;
   `Desugar.hs`'s relevant arm is marked unreachable today, so this
   should be fine but needs checking. Regenerate `generated/`
   (`make mhs-build` does this via `make resources`).
3. Tests: new golden `ambiguous_constructor_other_arity/` (the repro
   above, `.error` `YCHR-20012`); new
   `typecheck_constructor_arity_imported/` (a module that imports only
   `a` and uses bare `foo(1, 2)`; `.error` `YCHR-60008` naming
   `a:foo`); new `typecheck_invisible_constructor/` (pins that a
   constructor from an unimported module doesn't leak into arity
   checking). `RenameTest`: add a two-different-arities case to
   `ambiguousDataConTests`. Update the two existing warning tests that
   assumed per-arity dedup grouping. Full `make test`.
4. Docs: `type-system.md` §Known constructors (delete the "known gap"
   sentence) and §Constructor disambiguation (note ambiguity holds at
   any arity now). `language.md` (same point, one sentence).
   CHANGELOG breaking-change bullet (bare ctor declared by two
   imports is now `YCHR-20012` even when arities differ; used to
   resolve by arity and only warn `20102` on a mismatch).
5. Remove this entry from BUGS.md; add the new entry below (3a) for
   the qualified-wrong-arity case this fix deliberately leaves open.

## `YCHR-16002` ignores arity, and `host:foo(X)` in a rule head is accepted silently

**Documented claim.** PROJECT.md: function names "cannot collide with
constraint declarations in the same module" (`YCHR-16016`). That check
compares name and arity, so `f/1` as a constraint next to `f/2` as a
function is legal. Separately, `docs/reference/language.md` §Host
calls: host calls are allowed "in every evaluating position" — a rule
head is not one.

**Test (arity-blind 16002).**

    :- chr_constraint p/1, f/1.
    :- function f/2.
    f(X, Y) -> X + Y.
    p(X), f(X) ==> true.

    ychr check n1.chr

Expected: no error (`f(X)` in the head is the constraint `f/1`).
Actual: `YCHR-16002 '<n1>:f' is declared as a function but appears in
a rule head`.

**Test (host: in head accepted).**

    :- chr_constraint p/1, go/0.
    p(X), host:foo(X) ==> true.
    go <=> p(1).

    ychr check --Werror

Expected: an error, like an aggregate goal gives for `host:f(Y)`
(`YCHR-20041`). Actual: no diagnostic, exit 0. `ychr compile -t vm`
lists a constraint type `(qualified "host" "foo")`; the rule never
fires.

**Notes.** Both bugs are in the same code path and get one combined
fix. `Resolve.resolveProgram` (~line 281) calls `checkRuleHeads` with
`Set.map qualifiedToName functionNames` — arity dropped on the floor.
`checkRuleHeads` (~1299-1317) then compares by name only and reports
just the first rule per name. Separately, `renameCon`'s final
`NotAMacro` branch (Rename.hs ~1343-1386) calls `resolveName
ResolveTop` and `validateQualified`, and the latter happily lets
`host:foo` through as if it named a constraint.

**Fix sketch.** Owner decisions: D1 — new rename error code (next
free `200xx`; check what's free at implementation time, since this
file's other entries may also claim a code — 20045 is free as of this
writing), name `FunctionInHead`; retire `YCHR-16002` with a one-line
"retired, see YCHR-xxxxx" note in `Display.hs` (matching how `20004`
was retired). D2 — when building the function-name key set for this
check, exclude any `(name, arity)` that's *also* declared as a
constraint in the same module, so a real `f/1` constraint + `f/2`
function collision is instead caught by `Resolve`'s existing
`YCHR-16016` (this also fixes the same miss on the aggregate-goal
path). D3 — report every offending head conjunct, not just the first
(drop the current dedup-to-one-per-name; delete the
`function_in_rule_head_dedup` golden, which exists to pin the old
behavior). D4 — one constructor, `FunctionInHead Name Int`, covers
both a mis-arity function *and* a `host:` call in head position
(wording mirrors the existing `ConjunctIsFunction`/`20041` message).

1. **Rename.hs**: add `FunctionInHead Name Int` to `RenameError`. In
   `renameCon`'s last `NotAMacro` branch: if the resolved name/arity
   is a function name (`isFunctionName`), emit `FunctionInHead` and
   drop the head item; same check added for the "is this a known
   `host:`" case so a host call in head position gets the same error.
   `functionKeys`/`isFunctionName`'s building step (~line 839) now
   excludes `(name, arity)` pairs also declared as a `ConstraintDecl`
   in the same module (D2).
2. **Display.hs**: add the new code; message along the lines of
   "'<name>/<arity>' in a rule head is a function, not a constraint";
   hint: "rule heads must be constraints; call the function from the
   body or a guard instead". Retire `16002`
   (`resolveErrorCode`/`resolveErrorMsg` for `FunctionInRuleHead`)
   with a short "retired, see YCHR-<new>" comment.
3. **Resolve.hs**: delete `FunctionInRuleHead`, `checkRuleHeads`, and
   the `headErrors` plumbing that calls it; drop now-unused imports.
4. Goldens: update the three `function_in_rule_head_*` cases to the
   new code and message; delete `function_in_rule_head_dedup`; add
   `function_in_rule_head_other_arity` (positive — the `n1.chr` shape
   above, now compiles and the constraint fires), add
   `function_in_rule_head_host` (negative — the `host:foo` repro), add
   `constraint_function_collision_in_head` (same-module `f/1`
   constraint + `f/1` function sharing a head, expect `YCHR-16016`).
   Fix a stale comment in `constraint_function_collision.chr` that
   references the old 16002 interaction.
5. Docs: `language.md` (a head conjunct naming a function at that
   arity, or a host call, is an error — one sentence near "Heads are
   comma-separated constraint applications" and one in §Host calls).
   `PROJECT.md` one-sentence update near the function-collision
   paragraph.
6. CHANGELOG: note the arity fix, the new host-call check, and the
   "every conjunct reported" change; breaking-change bullet for the
   removed/added error constructors.
7. Remove this entry from BUGS.md (it covers both former entries).

## A DSL `extendClassType` is read as a declaration, not an extension

**Documented claim.** `docs/reference/dsl.md` maps
`:- extend_class_type (f(int) -> int).` to
`` `declaring` [extendClassType "f" ...] ``.

**Test.** In a Haskell test, compile with `compileParsedModules`:

    oc  = module' "oc" `exporting` [function "cl" 1]
            `declaring` [function "cl" 1]
            `withEquations` [equation "cl" [var "X"] [] (var "X")]
    ext = module' "ext" `importing` ["oc"]
            `declaring` [extendClassType "cl" [strT] intT]

and again with `extendClassType "nosuch" ...` in `ext`.

**Expected.** The same as the parsed directive: `YCHR-16005` for the
closed `cl`, `YCHR-20002` for `nosuch`.

**Actual.** `cl` gives `YCHR-20001 Ambiguous name 'cl/1'` (could be
`ext`, `oc`), and `nosuch` compiles with no error.

**Notes.** `declaring` appends to `Module.decls`, but the parser puts
an `ExtendClassTypeDecl` in `Module.extensionTypes`, which is the only
list Resolve reads extensions from. In `decls` it is counted as a
declaration by `Rename.declNameArity` (so `ext` seems to declare `cl`
itself) and is otherwise ignored. The `ExtendClassTypeDecl` arms of
`declNameArity` and `Repl.declarationsText` are only reached this way.

**Fix sketch.** Owner decisions: remove `ExtendClassTypeDecl` from
`Declaration` entirely (encode the invariant in the type — it was
never a real declaration); add a new DSL modifier
`withClassTypeExtensions` that appends to `extensionTypes` directly.
Also, while touching it: make `ExtendClassTypeDeclBody.argTypes`/
`returnType` non-`Maybe` (`[TypeExpr]`/`TypeExpr`), since the parser
always fills them — drops the dead `Just … <-` filters in
`collectExtensionSignatures`. One commit (separate from the
`requiring`-list fix below).

1. `Parsed.hs`: delete `ExtendClassTypeDecl ExtendClassTypeDeclBody`
   from `Declaration`; `Module.extensionTypes :: [Ann
   ExtendClassTypeDeclBody]` (keep the body type's name).
2. `Collected.hs`: `CollectedModule.extensionTypes` same type.
3. `Parser.hs`: `DirExtendClassTypeDecl [Ann
   ExtendClassTypeDeclBody]`; `convertExtendClassTypeDecl` returns the
   body directly, no `ExtendClassTypeDecl` wrapper.
4. `Rename.hs`: drop the `ExtendClassTypeDecl` arms of
   `declNameArity` and `validateImportLists`; replace the
   `renameDeclaration` arm with a dedicated
   `renameClassTypeExtension :: RenameCtx -> Ann
   ExtendClassTypeDeclBody -> Rename (Ann ExtendClassTypeDeclBody)`,
   called by `renameModule` over `m.extensionTypes`.
5. `Resolve.hs`: the five comprehensions that currently match
   `P.ExtendClassTypeDecl ed <- [d]` instead iterate
   `m.extensionTypes` directly.
6. `Repl.hs` `declarationsText`: drop both `ExtendClassTypeDecl` arms
   (now unreachable).
7. `DSL.hs`: `extendClassType :: Text -> [TypeExpr] -> TypeExpr ->
   ExtendClassTypeDeclBody` (bare body, no wrapper); new
   `withClassTypeExtensions :: Module -> [ExtendClassTypeDeclBody] ->
   Module`, same shape as the existing `withExtensions`/
   `withClassExtensions`; export both.
8. Check `embed/YCHR/Embedded/Generate/Instances.hs` still builds
   (Generic derivation).
9. Tests: update `DSLTest`'s `extendClassType` cases to expect a bare
   body; add a `withClassTypeExtensions` test; update `ParserTest` to
   target `m.extensionTypes`; new `RunTest` end-to-end cases via
   `compileParsedModules` + `withClassTypeExtensions`: closed `cl` →
   `ResolveErrors ExtendsClosedFunction` (16005); `nosuch` →
   `RenameErrors UnknownName "nosuch"` (20002).
10. Docs: `docs/reference/dsl.md` — remove `extendClassType` from the
    `Declaration` row, add `withClassExtensions` (currently missing
    from the doc) and `withClassTypeExtensions` to the `Module` row,
    with a worked mapping example.
11. CHANGELOG + breaking-change bullets (`Declaration` loses the
    constructor; `extensionTypes` element type changes; `DSL.
    extendClassType`'s return type changes; `argTypes`/`returnType`
    no longer `Maybe`).
12. Remove this entry from BUGS.md.

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
is "the same constructor" for ambiguity purposes — see the entry
above and the memory note on this).

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

**Notes.** This is the deliberately-left-open case from the "arity
checker misses a wrong-arity use" entry above (owner decision D3):
qualified lookup (`validateQualified` and friends) is keyed on
`(name, arity)` as a pair, so a qualified reference at the wrong
arity looks like a reference to a name that just isn't exported,
rather than "exported, but at a different arity". Since data
constructors are name-only, this is arguably the same bug as the
unqualified one, just on the qualified path.

**Fix sketch.** Not decided yet. When picked up: give qualified data
constructor lookup the same name-only treatment as the unqualified
path now has (R1 above) — check the module exports the *name* at any
arity, and if so, report an arity mismatch instead of "not exported".
Needs its own `(module, name)`-keyed (not `(module, name, arity)`)
visibility check for data constructors specifically; function/
constraint qualified lookup should stay arity-keyed, since those
*are* overloaded by arity in a sense functions are not (actually:
functions and constraints are also name+arity keyed for real
collisions — only data constructors are name-only). Verify against
`test/golden/typecheck_constructor_arity_imported` once entry 4
(arity checker) lands, since that fix changes what the unqualified
case reports.

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
  reserved for aggregates" (see the `?/1` macro entry above after its
  fix), but makes `?` unavailable as a constructor name forever.
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
