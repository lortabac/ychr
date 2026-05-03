# The constructor-name encoding bug in the YCHR type-checker

> **Status: resolved.** Sections 1–6 below describe the historical
> defect; section 8 shows the post-fix routing table. The fix lives in
> `src/YCHR/TypeCheck.hs` (a `conAlias :: Map (Text, Int) Name` index
> and a `canonicalizeConName` helper threaded through `typeOfAtom`,
> `typeOfCompound`, and `checkGuard`'s `GuardMatch` arm) and a small
> change in `typechecker/typechecker.chr` (`unknown_guard_getarg` now
> uses `tc_unify(ResultType, any, _)` instead of strict `=`, so it is
> sound when `ResultType` is already bound). The originally-failing
> typed `list(...)` parameters on `all_nonvar_list/1`,
> `filter_consistent/2`, and `sig_args_consistent/2` have been
> restored. Section 7 (qualified-in-head HNF interaction) is partially
> resolved as a side effect of the fix; the remaining residual
> limitation is documented there.

## Historical TL;DR

`typechecker/typechecker.chr` contains rules that look up the
declared shape of a data constructor (`delegate_guard_getarg`,
`constructor_match`, the lookups in `typeOfAtom` /
`typeOfCompound`). **All of these silently never succeeded.** The two
sides of the lookup encoded the constructor name differently — one
side carried the module prefix, the other did not — so the
strings never compared equal. As a result, the value-level
constructor-typing pathway was dead since it was written, and
every constructor in a pattern (or as a bare atom value) collapsed
to the dynamic type `any`.

---

## 1. The two rules at the centre of the problem

In `typechecker/typechecker.chr`, two rules are responsible for
propagating the type of a known data constructor into the wider
type-check:

```prolog
constructor_match @
    con_sig(ConName, Sig) \
        check_constructor_use(ConName, ArgTypes, ResultTypeVar, Ctx) <=>
    Fresh is copy_term(term(Sig)),
    FreshParent is sig_fst(Fresh),
    FreshFields is sig_snd(Fresh),
    check_arg_list(FreshFields, ArgTypes, Ctx),
    tc_unify(ResultTypeVar, FreshParent, Ctx).

delegate_guard_getarg @
    con_sig(ConName, Sig) \
        check_guard_getarg(ResultType, TermType, ConName, FieldIndex, Ctx) <=>
    Fresh is copy_term(term(Sig)),
    FreshParent is sig_fst(Fresh),
    FreshFields is sig_snd(Fresh),
    tc_unify(TermType, FreshParent, Ctx),
    FieldType is nth(FieldIndex, FreshFields),
    tc_unify(ResultType, FieldType, Ctx).
```

Both are **simpagation rules** of the form
`con_sig(N, S) \ check_X(..., N, ...) <=> ...`. The shared variable
`ConName` between the kept and removed head means the rule fires
only for a pair where the constructor name on both sides is *equal*
(via Prolog `==` semantics applied by the CHR engine).

A third rule provides the gradual-typing fallback when the join
fails:

```prolog
unknown_guard_getarg @
    check_guard_getarg(ResultType, _, _, _, _) <=> ResultType = any.
```

`delegate_guard_getarg` is declared *before* `unknown_guard_getarg`,
so under the refined operational semantics the engine tries the
delegate first; the unknown variant fires only when no `con_sig`
matches.

## 2. The symptom

When `ychr check typechecker/typechecker.chr` runs (the
self-check), or any user program is type-checked, the join in
`delegate_guard_getarg` and `constructor_match` **never
succeeds**, even when both constraints are present in the store
with the "same" constructor name. The unknown variant always
fires.

This was hidden until the original task added typed `list(...)`
parameters to a few helper functions in `typechecker.chr`. With
list-typed parameters, `unknown_guard_getarg`'s body
`ResultType = any` started failing at runtime: the `ResultType`
variable had been bound to a concrete `list(any)` by an earlier
constraint (the recursive body call), and unifying `list(any)`
with the atom `any` fails. The runtime error surfaced the
underlying issue.

## 3. The two encoding paths in detail

There are two places in `src/YCHR/TypeCheck.hs` that emit a
constructor name into a CHR constraint, and one place that does
the corresponding lookup. They use different sources for the name,
and those sources have been transformed differently by the
front-end pipeline:

### 3a. The "declarations" side — `tellConSigs`

`tellConSigs` (`src/YCHR/TypeCheck.hs:231-246`) walks every type
definition the program knows about and emits one `con_sig` per
constructor:

```haskell
tellConstraint
  (Qualified "typechecker" "con_sig")
  [VAtom (flattenName dc.conName), sig]
```

`dc.conName` here is whatever the renamer left in the
`DataConstructor`. Looking at `renameDataConstructor`
(`src/YCHR/Rename.hs:563-568`):

```haskell
renameDataConstructor ctx dc =
  DataConstructor
    { conName = Qualified ctx.currentModule.name (unqualifiedText dc.conName),
      conArgs = map (renameTypeExpr ctx) dc.conArgs
    }
```

Every constructor's name is **unconditionally rewritten to the
qualified form** `Qualified <currentModule> <name>`. So for the
cons constructor of `prelude:list` (declared in `prelude.chr` as
`:- chr_type list(T) ---> [] ; [T|list(T)].`), `dc.conName` ends
up as `Qualified "prelude" "."`. `flattenName`
(`src/YCHR/Types.hs:102-104`) then produces the flat string
`"prelude:."` and `con_sig` is told as
`con_sig(VAtom "prelude:.", sig(...))`.

### 3b. The "uses in patterns" side — `checkGuard` / `D.GuardGetArg`

When the type-checker processes a rule head or a function-equation
parameter, the desugarer has already run **Head Normal Form (HNF)**
over the head, replacing every compound-term pattern with a fresh
variable plus explicit `D.GuardMatch` and `D.GuardGetArg` guards
(`src/YCHR/Desugar.hs:227-279`):

```haskell
decomposeCompound st parentVar cname cargs =
  let matchGuard = D.GuardMatch (VarTerm parentVar) cname (length cargs)
      st' = st {hnfGuards = matchGuard : st.hnfGuards}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] cargs)
```

The `cname` here is the constructor functor as the desugarer
received it from the renamer. For a head like `[H|T]`, the chain
is:

1. Parser produces `Compound "." [H, T]` (the cons functor in
   YCHR is the dot atom, see `Parser.hs:653-654`).
2. The Parser→AST converter wraps it as
   `CompoundTerm (Unqualified ".") [...]`.
3. `renameCon` (`Rename.hs:357-358`) and
   `renameResolvedEquation` (`Rename.hs:344`) call
   `renameTerm ... NoResolve` on argument positions.
4. The `NoResolve` branch of `renameTerm`
   (`Rename.hs:417-426`):

   ```haskell
   CompoundTerm name args -> do
       let childMode = case mode of
             NoResolve -> NoResolve
             ResolveTop -> NoResolve
             ResolveAll -> ResolveAll
       renamedArgs <- traverse (renameTerm ctx loc origin childMode) args
       newName <- case mode of
         NoResolve -> pure name             -- ← name is NOT touched
         _ -> resolveName mode ctx loc origin name (length args)
       pure (CompoundTerm newName renamedArgs)
   ```

   In `NoResolve` mode the compound's `name` field is returned
   verbatim — no resolution, no module qualification. The cons
   functor stays as `Unqualified "."`.

5. The HNF passes that name straight into
   `D.GuardMatch (VarTerm parentVar) (Unqualified ".") 2`.

6. `checkGuard` for `D.GuardGetArg` in
   `src/YCHR/TypeCheck.hs:355-365`:

   ```haskell
   checkGuard cctx lastConName (D.GuardGetArg varName term idx) = do
     ...
     conName <- case lastConName of
       Just cn -> pure cn
       Nothing -> pure (Unqualified varName)
     termType <- typeOfTerm cctx term
     ctx <- freshCtx cctx
     tellConstraint
       (Qualified "typechecker" "check_guard_getarg")
       [resultTypeVar, termType, VAtom (flattenName conName), VInt idx, ctx]
     ...
   ```

   `lastConName` came from the matching `D.GuardMatch` and is
   `Unqualified "."`. `flattenName (Unqualified ".")` produces the
   bare string `"."`, and `check_guard_getarg` is told with that.

### 3c. The mismatch

The two strings — `"prelude:."` from the declaration side and
`"."` from the use side — are not equal. The shared `ConName` in
`delegate_guard_getarg`'s head is supposed to bind to the same
runtime value on both sides; it cannot, because the values differ.
The CHR engine correctly reports no match, the rule is skipped,
and `unknown_guard_getarg` runs instead.

## 4. The same bug disables the value-level constructor lookups

`tellConSigs` is the side that *populates* `con_sig`. The
`TypeCheckEnv.conMap` is the *Haskell-side mirror* of the same
information, built once at the start of `typeCheckProgram`
(`src/YCHR/TypeCheck.hs:98-104`):

```haskell
buildConMap :: [TypeDefinition] -> Map Name (TypeDefinition, DataConstructor)
buildConMap tds =
  Map.fromList
    [ (dc.conName, (td, dc))
    | td <- tds, dc <- td.constructors
    ]
```

So `conMap` is keyed by the **qualified** `dc.conName` —
`Qualified "prelude" "."` for cons, `Qualified "prelude" "true"`
for `true`, etc.

Now look at the call sites. `typeOfAtom`
(`src/YCHR/TypeCheck.hs:476-485`):

```haskell
typeOfAtom :: (CheckEffects es) => CheckCtx -> Name -> Eff es Value
typeOfAtom cctx name = do
  env <- ask @TypeCheckEnv
  case Map.lookup name env.conMap of
    Just _ -> ...emit check_constructor_use, return concrete type...
    Nothing -> pure (VAtom "any")
```

Its only caller is `typeOfTerm`'s `AtomTerm` branch
(`src/YCHR/TypeCheck.hs:471-472`):

```haskell
typeOfTerm cctx (AtomTerm s) =
  typeOfAtom cctx (Unqualified s)
```

That `Unqualified s` is the bare atom name from the parsed term
(after rename, atoms in `NoResolve` mode stay as `AtomTerm`).
`Map.lookup (Unqualified "true") conMap` — when `conMap` is keyed
by `Qualified "prelude" "true"` — silently misses every time.

Same story in `typeOfCompound`'s cons branch
(`src/YCHR/TypeCheck.hs:489-501`) and its general branch
(`src/YCHR/TypeCheck.hs:517-525`): both use `Map.lookup` with the
incoming (typically `Unqualified`) name against a `Qualified`-keyed
map.

So `check_constructor_use` is **also rarely told**, and the
constructor-typing pathway gets two layers of "silently fall
through to `any`": the lookups don't find anything, so
`check_constructor_use` doesn't fire, so `constructor_match` has
nothing to join with, so even if the encodings matched, the
pathway would be empty.

## 5. Empirical confirmation

I instrumented the typechecker rules with `host:write` traces.
With the unmodified file (no typed function declarations), running
`ychr check typechecker/typechecker.chr`:

| Trace | Count |
|---|---|
| `con_sig(_, _) ==> host:write("CONSIG_TOLD")` | 12 |
| `check_guard_getarg(_, _, _, _, _) ==> host:write("CHECK_SEEN")` | 44 |
| Inside body of `delegate_guard_getarg` | **0** |
| Inside body of `constructor_match` | **0** |
| Inside body of `unknown_guard_getarg` | 44 |

Then I narrowed the join with two propagation rules to discover
which `ConName` values appeared on each side:

```prolog
trace1 @ con_sig(N, _) ==> N == 'prelude:.' | host:write("CONSIG_HAS_PRELUDE_DOT").
trace2 @ check_guard_getarg(_, _, N, _, _) ==> N == '.' | host:write("CHECK_HAS_BARE_DOT").
```

| Trace | Count |
|---|---|
| `CONSIG_HAS_PRELUDE_DOT` | 1 (the cons constructor of prelude:list) |
| `CHECK_HAS_BARE_DOT` | 34 (every cons-pattern HNF guard in the file) |

The two strings exist in the store but are different atoms. The
join cannot succeed.

## 6. Cascading consequences

Because the lookups silently fail, the type system has degraded to
a near-trivial one in any place a constructor would have provided
type information:

- `[H|T]` patterns in heads or equations don't propagate `H : T`
  and `Ts : list(T)`; they degrade to anything.
- `tcon(C, A)`, `fun(A, R)`, `sig(X, Y)` head patterns in the
  typechecker.chr's own rules don't propagate field types.
- Bare constructor atoms in body or guard position
  (`true`, `false`, `red`, `green`, ...) type as `any`.
- Function equations matching constructors in their parameters
  don't propagate to those parameters' types.

Most existing user programs and tests "type-check" only because
this degradation hides every constructor-driven inconsistency.

## 7. The user-qualified-syntax twist

When a user writes `module:name` in source — for example,
`tcon(prelude:bool, [])` in the typechecker's own
`delegate_guard_bool` rule — the path is different and partially
works.

The parser converts `Compound ":" [Atom "prelude", Atom "bool"]`
**directly** into `CompoundTerm (Qualified "prelude" "bool") []`
at the AST level (`src/YCHR/Parser.hs:373-377`):

```haskell
Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
  CompoundTerm (Qualified m n) []
```

So the AST starts qualified. Then:

- **In a body position**, `typeOfCompound` receives the
  `Qualified "prelude" "bool"` and does `Map.lookup` against
  `conMap`, which is also keyed by `Qualified` — so the lookup
  **succeeds**. `check_constructor_use` is told with
  `flattenName (Qualified "prelude" "bool")` =
  `"prelude:bool"`, which equals the `con_sig` side's encoding.
  `constructor_match` fires correctly. This is the one case that
  works today.

- **In a head position**, the desugarer's `decomposeCompound`
  special-cases `Qualified` cnames and **rewrites them into a
  `:`-compound match** (`Desugar.hs:231-235`):

   ```haskell
   decomposeCompound st parentVar (Qualified m n) cargs =
     let inner = case cargs of
           [] -> AtomTerm n
           _ -> CompoundTerm (Unqualified n) cargs
      in decomposeCompound st parentVar (Unqualified ":") [AtomTerm m, inner]
   ```

   This is correct at the runtime level — at runtime, a qualified
   atom like `prelude:bool` is encoded as
   `VTerm ":" [VAtom "prelude", VAtom "bool"]` (see
   `compileTerm`, `src/YCHR/Compile.hs:425-432`), so a
   `:`-compound match correctly picks it up. **But**: the
   `D.GuardMatch` produced by the rewrite has `cname = ":"`. The
   subsequent `D.GuardGetArg` then emits
   `check_guard_getarg(..., VAtom ":", ..., ...)`, and the
   constructor name the user actually wrote (`prelude:bool`) is
   nowhere in that constraint. There is no `con_sig(VAtom ":",
   ...)` to join against — `:` is the term-encoding wrapper, not
   a real declared constructor — so the head-position qualified
   case **also degrades to `any`**.

In short: qualified-in-body works (both encodings happen to land
on `"prelude:bool"`); qualified-in-head doesn't (the
constructor name gets absorbed into the `:`-compound rewrite).

## 8. Routing table (post-fix)

| Form | Where written | Reaches `con_sig`? |
|---|---|---|
| `red` (bare atom) | body | **Yes** — `typeOfAtom` canonicalizes `Unqualified "red"` to `Qualified <decl-mod> "red"` via `conAlias` |
| `red` (bare atom) | head | **Yes** — same path; the HNF `GuardEqual` ultimately runs `typeOfTerm` on the atom |
| `[H\|T]` (bare cons) | head | **Yes** — `GuardMatch` canonicalizes `"."` to `prelude:.`; the following `GuardGetArg` emits `check_guard_getarg(..., "prelude:.", ...)` matching `con_sig` |
| `tcon(C, A)` (own-module bare) | head | **Yes** — same canonicalization for `tcon` against the local module |
| `prelude:red` | body | **Yes** — `Qualified` names are passed through `canonicalizeConName` unchanged and already match `con_sig` |
| `prelude:red(X, Y)` | head (non-nullary) | **Yes** — the HNF `:`-rewrite leaves the inner functor as `Unqualified "red"`, which canonicalization resolves to `Qualified "prelude" "red"` |
| `prelude:red` | head (nullary) | **Limited** — see section 7. The HNF rewrite emits two `GuardEqual`s against `prelude` and `red` atoms, which type the synthetic `_hnf_*` variables but do not refine the user-visible parent term beyond the type the enclosing constraint signature already provides. |

Only the last row remains as a documented limitation; in practice no
in-tree code exercises it.

## 9. Why this remained hidden (historical)

Because the failure was silent — every miss fell into the gradual
"unknown → `any`" path — no one had a reason to look. The
type-checker accepted everything, so it appeared to work. The
self-check passed because none of the typechecker's own rules
contained a *strong enough* type annotation to surface a real
inconsistency: the absence of constructor type propagation just
made the type system maximally permissive. The bug only came to
light when someone tried to add `list(...)`-typed parameters to
helper functions in `typechecker.chr` and discovered that the
`unknown_guard_getarg` fallback was unsound under the new
constraints — at which point the empirical chain above could be
traced backwards to the encoding mismatch.

## 10. Resolution notes

The fix is one-sided: the type checker performs the resolution work
that the renamer cannot (qualifying constructor names in the AST
would change the runtime encoding — see `compileTerm` at
`src/YCHR/Compile.hs:425-432` — and break list-pattern matches).
Specifically:

- `TypeCheckEnv` gains a `conAlias :: Map (Text, Int) Name` index
  built from `prog.typeDefinitions`. Only `(text, arity)` pairs with
  a unique declared constructor are included; ambiguous pairs are
  dropped so the type checker treats them as unknown rather than
  guessing.
- `canonicalizeConName env name arity` returns the qualified form
  when one exists; otherwise the name is returned unchanged.
- `typeOfAtom`, `typeOfCompound` (cons + general branches collapsed),
  and `checkGuard`'s `GuardMatch` arm all canonicalize the incoming
  name before `Map.lookup`/`Set.member` and before forming the
  `flattenName` payload of any CHR constraint.
- `unknown_guard_getarg` in `typechecker.chr` was changed from
  `ResultType = any` to `tc_unify(ResultType, any, 0)` so that the
  fallback is sound when `ResultType` is already bound to a
  non-`any` type by an earlier constraint.

Verification:

- The previously-failing typed signatures on `all_nonvar_list/1`,
  `filter_consistent/2`, and `sig_args_consistent/2` are restored;
  `ychr check typechecker/typechecker.chr` exits 0.
- Two new golden tests under `test/golden/`:
  `typecheck_list_pattern` (positive: typed `list(int)` signature
  with `[H|T]` pattern) and `typecheck_list_pattern_bad` (negative:
  list-pattern match on a head argument declared `int`, expects
  `YCHR-60001`).
- Full Haskell suite (`cabal test`) and Scheme suite
  (`python3 -m pytest test/scheme/`) pass.
