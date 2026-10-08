# Invariants Not Enforced in the Types

This document lists invariants that the YCHR implementation depends on
but the type system does not enforce. Each entry is a candidate for a
future tightening pass.

The catalogue is organized by category, following the framing of the
original audit:

1. Uses of `error` / `runtimeErrorS` for "can't happen" cases.
2. Data types that admit invalid states.
3. Documented invariants worth promoting into types.
4. Undocumented invariants the implementation relies on.
5. Cross-cutting compiler ↔ runtime contracts.
6. Clean-up ideas: duplications and structural improvements that are
   not themselves invariants (added after the Haskell style pass).

Entries are concrete (file:line, code snippet) so they can be picked up
as standalone tasks.

For the format, see `SCHEME_BACKEND_GAPS.md` — terse, fix-shaped,
removable when closed.

## Already closed (reference)

- **Constraint and function names are qualified after the resolve
  phase**. Encoded by introducing `Types.QualifiedName` and
  `Types.QualifiedConstraint` and tightening `Resolved.hs` /
  `Desugared.hs` to use them. Removed two `error` calls in
  `src/YCHR/Internal/Desugar.hs` that previously guarded the invariant. (Some
  rare paths still use `Types.qualifiedToName` to feed legacy helpers
  that operate on `Name`; those helpers can be migrated incrementally.)

- **Tell-side constraint arguments are evaluated expressions, not
  patterns.** Encoded by replacing `Desugared.BodyConstraint
  QualifiedConstraint` (a `[Term]` carrier) with
  `Desugared.BodyTell QualifiedName [Expr]`. Rule bodies and top-level
  goals both flow through `BodyTell`; head occurrence patterns keep
  `HeadConstraint` / `Term` because matching still operates on data
  shapes. `Compile.compileBodyGoal`'s `BodyTell` arm pre-walks top-
  level `VarExpr` args to lift fresh logical variables (preserving
  the `foo(X)` convenience), then routes the args through `compileExpr`
  — the same path used by `is` RHS. (`=` is the deliberate exception:
  its operands are non-evaluating, so `BodyUnify` routes them through
  `R.exprToTerm` and `compileTerm`, mirroring the query-side
  `Run.exprToValue`.) The interpreter mirrors the evaluated path via
  `Run.evalNestedExpr`. `Resolve.termToExpr` learns
  to canonicalize bare-named functions when exactly one declared
  function shares the name (e.g. `+(2, 1)` → `CallExpr prelude:+`),
  so operator-style expressions in tell-arg position evaluate without
  forcing the user to fully qualify. Quoting (`quote(foo(X))`) is the
  opt-out for callers who want a literal data term.

- **Head Normal Form: post-HNF head args are variables or wildcards.**
  Encoded by introducing `Types.HeadArg = HeadVar Text | HeadWildcard`
  and `Types.HeadConstraint`, narrowing `Desugared.Head`'s `kept`/
  `removed`, `Desugared.Equation.params`,
  `Compile.Types.Occurrence.activeArgs`, and
  `Compile.Types.Partner.constraint` to the new types.
  `Desugar.normalizeArg` is the producer; the boundary helper
  `headArgToTerm` (in `YCHR.Types`) survives for the one place that
  still needs a `Term`, the lambda spelling in `Resolved.hs`. The list-
  comprehension drops in `Compile.buildVarMap` /
  `buildEquationVarMap` are now exhaustive matches on
  `HeadVar`/`HeadWildcard` instead of silent wide-`Term` filters.

- **Constraint identifiers do not flow through unification or term
  positions.** Encoded by splitting the VM IR into `ValExpr` (value-
  producing) and `IdExpr` (constraint-id-producing) ADTs, with a
  `CallArg = AVal ValExpr | AId IdExpr` wrapper at procedure-call
  boundaries. `Stmt` operands narrow accordingly: `Store`/`Kill`/
  `AddHistory` take `IdExpr`; `If`/`Foreach` conditions and `Return`/
  `ExprStmt` take `ValExpr`; `Let`/`Assign` split into `LetVal`/`LetId`
  and `AssignVal`/`AssignId`. The interpreter splits `evalExpr` into
  `evalValExpr :: ValExpr -> Eff es Value` and `evalIdExpr :: IdExpr ->
  Eff es SuspensionId`, and the local environment splits into
  `envValues` and `envIds`, keyed by the locals' slots rather than
  their names since the interpreter moved to its own slot phase (see
  "The interpreter's slot phase mirrors the VM AST" below).
  `RuntimeVal` is removed; cross-procedure args use `Runtime.Types.CallVal`
  (`CVal Value | CId SuspensionId`). `HostCallFn` narrows to
  `[Value] -> Eff es Value`. Closes seven interpreter `runtimeErrorS`
  sites (Store, Kill, `expectConstraintId` for AddHistory/NotInHistory,
  Alive, IdEqual, IsConstraintType, FieldGet) plus the `toValue` panic
  in `Registry.hs`.

- **Boolean-position operands of `If`/`Not`/`And`/`Or` are statically
  booleans.** Encoded by introducing a third positional IR kind,
  `Types.BoolExpr`, that holds the syntactically-bool constructors
  (`BLit`, `BNot`, `BAnd`, `BOr`, `BMatchTerm`, `BEqual`, `BIdEqual`,
  `BAlive`, `BIsConstraintType`, `BNotInHistory`, `BUnify`,
  `BFromVal`, `BEvalDeep`). `Stmt`'s `If` condition narrows to
  `BoolExpr`, and a new `BoolExprStmt` carries discarded boolean
  expressions (e.g. tell-side `BUnify`). The interpreter gains
  `evalBoolExpr :: BoolExpr -> Eff es Bool` and `evalBoolExprDeep`,
  with the `If` case now `b <- evalBoolExpr cond; if b then ... else
  ...` — no shape check. `BFromVal !ValExpr` is the explicit bridge
  for user-written value expressions used in bool position (e.g.
  user-function calls in guards, the early-drop result variable);
  it carries a single named runtime check, replacing the four
  `evalValExpr` shape errors. This bridge is a permanent part of
  the design: user-defined functions deliberately remain unannotated,
  so the value-to-bool coercion stays explicit.

- **A dereferenced value's variable cell is unbound.** Encoded by a
  module-private combinator in `src/YCHR/Internal/Runtime/Var.hs`:

  ```haskell
  withUnboundVar ::
    Var -> (VarId -> [SuspensionId] -> Chr a) -> (Value -> Chr a) -> Chr a
  ```

  It reads the cell behind a `VVar` that `deref` has just returned and
  hands the contents to the first continuation. The caller never sees
  a `VarState`, so it has no impossible arm to write: the second
  continuation is an ordinary handler taking the value the cell turned
  out to hold, and every caller's is a real one (re-enter `unify` on
  that value; skip the observer registration; answer `Nothing`).

  It is continuation-passing rather than a returned sum type on
  purpose. The obvious encoding — `data Deref = DUnbound !Var !VarId
  ![SuspensionId] | DVal !Value` returned by a `derefView` — was
  written first and rejected: unification reaches it at every node of
  every term it walks, and it allocates a box per call for no
  offsetting benefit. (The difference did not separate from
  `typecheck/pairs_library`'s run-to-run noise, which is roughly ±10%
  on the machine this was measured on — but the CPS form costs nothing
  to prefer, since inlined it compiles to the same `case` the
  panicking version had.)

  All three `error "unify': unexpected Bound after deref"` calls were
  in `unify'` itself; they become `withUnboundVar`. The other two, in
  `unifiable`'s `uni'`, simply go away: that function only overwrites
  cells through its trail and never merges observer lists, so it read
  the `VarState` purely to assert on it, and now reads nothing.
  `addObserver` and `getVarId` never panicked — they had ordinary
  `Bound {} -> pure ()` / `pure Nothing` arms — but they went through
  `withUnboundVar` too, so the raw `VarState` read has exactly one
  home in the module.

  What the change gives up: the three `onBound` bodies in `unify'` are
  dead by construction, and a crash is a louder signal than a
  plausible recovery. If some future caller broke the deref invariant,
  the old code would have said so and the new code will quietly unify
  the bound value instead. That is the deliberate trade — the arm has
  to exist either way, and a defensible handler beats a panic for
  something a caller cannot cause today.

  The exported `deref :: Value -> Chr Value` is untouched — it is
  public API with many external callers. `unifiable`'s trail keeps raw
  `VarState` read/restore, which is fine inside the one module allowed
  to touch the constructors: `Var.hs` no longer re-exports `VarState
  (..)`, and `Runtime/Types.hs` — which must keep exporting them, since
  `Value`/`Var`/`VarState` are mutually recursive and so cannot be
  split across modules — says so in the type's haddock.

- **A propagation-history tuple is ordered by head position.**
  Encoded by `VM.Types.HistoryIds`, a newtype over `[IdExpr]` whose
  constructor is not exported. `mkHistoryIds :: Ord k => [(k, IdExpr)]
  -> HistoryIds` is the intended producer and does the sort;
  `historyIdsList` is the accessor; `historyIdsFromSerialized` is the
  documented trust boundary for `VM.SExpr` deserialization, where the
  head positions the order came from are not part of the serialized
  form. `AddHistory` and `BNotInHistory` carry `HistoryIds`, and
  `Compile.buildHistoryIds` became the position-tagged producer (its
  local `sortOn` moved into the smart constructor).

  Be honest about how much this enforces. `mkHistoryIds` is
  polymorphic in the key, so `mkHistoryIds (zip [0 ..] ids)` is an
  identity function on the list — which is exactly what the two test
  helpers do — and `historyIdsFromSerialized` will take any list at
  all. Any module inside the package can still build a
  wrongly-ordered `HistoryIds`. What the newtype buys is that the
  operand cannot be a bare `[IdExpr]` by accident, and that the one
  place the compiler builds one has to name the positions it is
  ordering by. Typing the key as `HeadPosition` would go further, but
  `VM.Types` cannot import `Compile.Types`.

  Note what is deliberately *not* encoded: the tuple is a
  head-position-indexed tuple, not a set — see §4's history entry for
  why a set would be wrong.

- **A partner's constraint type resolved in the symbol table.**
  Encoded by making `Compile.Occurrences.lookupCType` return `Maybe
  ConstraintType`, dropping the `ConstraintType (-1)` sentinel.
  `mkOccurrence` returns `Maybe Occurrence` and `ruleOccurrences`
  `catMaybes` the result, so an occurrence with an unresolvable
  partner is dropped rather than compiled against a placeholder type.
  Compilation still always fails: `lookupCType` emits a diagnostic on
  every miss, `Compile.compile` aborts as soon as any diagnostic was
  emitted, and `collectOccurrences` has exactly one caller. The one
  behavioural difference is diagnostic completeness — a dropped
  occurrence is not walked by `genConstraintProcs`, so an
  `UnboundVariable` its rule body would also have reported is no
  longer emitted in the same run. That mildly undercuts `compile`'s
  "collect errors from every sub-pass" intent, and is the reason to
  prefer dropping over any cleverer recovery only because the miss
  branch looks unreachable in practice: the renamer rejects an
  undeclared head constraint first (`YCHR-20002`), so `YCHR-40001`
  never fires from the public pipeline, and there is no golden test
  for it.

  The runtime's `getStoreSnapshot` keeps its `findWithDefault` —
  pinned by `StoreTest.hs`'s "empty snapshot for unknown type", and a
  reasonable defence for the store API generally — but it is no longer
  the sentinel's safety net.

- **HNF guards and lifted lambdas accumulate in emission order.**
  Encoded by switching `Desugar.HnfState.guards` and
  `Desugar.LiftState.liftedFunctions` from reverse-prepended lists to
  `Data.Sequence.Seq` with `(|>)`, so each consumer is a `toList`
  rather than a `reverse` that has to happen exactly once. The second
  also fixes a real (if benign) discrepancy this document previously
  got wrong: `liftedFunctions` was never reversed at all, so reverse
  discovery order leaked into `D.Program.functions` (and a nested
  lambda came out after its enclosing one). Downstream is
  order-insensitive — `buildEvaluables` and `buildCallables` key by
  name, and
  `checkExhaustiveness` runs on the pre-lift program — so what shifts
  is presentation: generated-procedure emission order, and the
  relative order of type-check diagnostics coming from two different
  lambdas, since the checker runs on the post-lift program and nothing
  sorts its output. Golden `.error` files match by containment, so
  none of that is pinned.

- **Lambdas in a `gen-driver` goal are rejected, not panicked on.**
  `app/Main.hs`'s `gen-driver` path fed goal expressions straight to
  `generateDriver` with no lambda lifting (unlike `Run.hs`, which
  lifts first), so `SchemeDriver.exprToScheme`'s `error` was reachable
  from the command line: `ychr gen-driver -g 'p(fun(X) -> X + 1 end,
  R)'` panicked. It is now a real diagnostic — `Error`'s
  `LambdasInSchemeDriver` (YCHR-50004), a sibling of the REPL's
  `LambdasInLiveQuery` — raised by `generateDriver`, whose type became
  `... -> Either Error Text`. Lifting the lambda instead is not
  available here: the driver is a standalone script over an
  *already generated* library, so it can neither add the lifted
  `__lambda_N` procedure nor add an entry for it to that library's
  callables table. `exprToScheme`'s lambda arm remains an `error`,
  but it is now an internal invariant behind that check rather than a
  user-facing gap, and it closes with the other two `LambdaExpr`
  panics when `R.Expr` grows a phase index (see §1).

- **`Occurrence.conArity` is derived, not stored.** Deleted the
  redundant `Int` field and replaced it with `occurrenceArity ::
  Occurrence -> Int` (`Compile.Types`), defined as `length
  occ.activeArgs`. `Desugar.normalizeArg` maps every head term to
  exactly one `HeadArg`, so at the field's single birth site
  (`mkOccurrence`) it was literally `length activeCon.args` —
  identical to `activeArgs` — and nothing ever cross-checked the two.
  The two readers (the occurrence-map key in `collectOccurrences` and
  `argNames` in `Compile.inScopeBeforeLoop`) now go through the
  accessor, so drift between the stored arity and the argument list is
  unrepresentable. No behavioural change: the renamer already rejects
  an arity-mismatched head constraint (`YCHR-20002`). The §2 entry
  "Compiler IR carries unchecked arity fields" retains the `Partner`
  and `IndexCondition` items.

- **`suspArg` bounds are checked, mirroring `getConstraintArg`.** The
  pure projection in `Store.hs` did `sargs !! idx` with no guard, so an
  out-of-range `ArgIndex` pushed into a `Foreach` and read by
  `checkConditions` (`Interpreter.hs`) surfaced as a bare `Prelude.!!`
  failure with no context. It now raises the same style of named
  `"suspArg: index N out of bounds"` error as its monadic twin. The
  index is still an `Int`; the `ArgIndex` / non-negative
  representation work in §2 remains the structural fix.

- **The reactivation observer list is LIFO (most-recently registered
  first).** §3's entry asked for a named `Note`; it now lives in
  `src/YCHR/Internal/Runtime/Var.hs` as `Note [Observer registration
  order]`, so the prepend order at every registration site is called
  out rather than implied by the code.

- **VM IR index/arity slots are non-negative.** `ArgIndex`,
  `GetArg`'s index and `BMatchTerm`'s arity — and the desugared
  `GuardMatch` / `GuardGetArg` slots that feed them — are `Word` in
  `VM/Types.hs`, `Desugared.hs` and `Interpreter/Slots.hs`, so a
  negative index or arity is unrepresentable in the IR. Because
  `fromInteger` would silently wrap a negative serialized slot under
  `Word`, `VM.SExpr`'s decoder gained a checked `nonNegative` helper
  used at all four decode sites (`GetArg`, `FieldArg`'s `ArgIndex`,
  `BMatchTerm`'s arity, `Foreach` conditions), which rejects a negative
  or out-of-`Word` value by name. Rejection is pinned by the
  "non-negative slots" group in `test/YCHR/VM/SExprTest.hs`. The
  runtime store accessors (`suspArg`, `getConstraintArg`) still take an
  `Int` with an upper-bound guard, converted from the `Word` slot at
  the call site; §1's `getConstraintArg` entry is closed by this, since
  the compiler can no longer produce a negative index.

- **`VM.Program`'s type and rule counts are derived, not stored.** The
  redundant `numTypes` / `numRules` fields are gone; every use is
  `length typeNames` / `length ruleNames` (`VM/Types.hs`,
  `Compile.hs`, `SExpr.hs`, `Backend/Scheme.hs`). The s-expression
  header still carries the two integers, so the decoder now holds them
  against the lists they count through `checkDeclaredCount` and rejects
  a disagreeing unit (`test/YCHR/VM/SExprTest.hs`, "declared counts"
  group); `docs/reference/vm.md` documents them as redundant. This
  closes the `VM.Program` paragraph of §2's "Compiler IR carries
  unchecked arity fields"; the `Partner` / `IndexCondition` items
  remain.


## 1. `error` / `runtimeErrorS` for "can't happen" cases

Each of these crashes if the documented runtime invariant is violated.
A stronger type or a checked smart constructor would turn the runtime
panic into a compile-time error.

### `getArg` operand and bounds — `src/YCHR/Internal/Runtime/Var.hs:356-357`

```haskell
| otherwise -> error $ "getArg: index " ++ show idx ++ " out of bounds"
_ -> error "getArg: not a compound term"
```

`getArg` is partial on shape (must be `VTerm`) and on index. The
index half is now narrowed to its upper bound: the index is a `Word`
(see the closed VM IR entry above), so no negative value can reach it,
but the present check remains a partial `error`. A typed
term-projection API keyed on a verified `(VTerm functor arity)` handle
would close both halves.

### `lookupSusp` — `src/YCHR/Internal/Runtime/Store.hs:72`

```haskell
Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid
```

Every `SuspensionId` in circulation must have been allocated by
`createConstraint`. The header comment calls a miss "a runtime
invariant violation, not a user-facing failure" — exactly the case for
a typed handle (e.g. an opaque newtype that can only be created by the
allocation API).

### Remaining interpreter shape checks — `src/YCHR/Internal/Runtime/Interpreter.hs`

After the value-vs-id and bool splits, these sites remain that are
name- or index-resolution invariants rather than shape invariants:

| Site                                | Required precondition                     |
|-------------------------------------|-------------------------------------------|
| `callProc` (unknown name)           | name resolves in `procMap`                |
| `callProcAt` (stale index)          | index resolves in `procEntries`           |
| `evalValExpr (SVar slot name)`      | slot in `envValues`                       |
| `invokeHostCall` (unknown)          | name in registry                          |

The first closes for compiler output — see §5 "Closed procedure-name
set" — and stays a runtime error only for a hand-built `Program` that
the interpreter is handed directly. The second is unreachable by
construction: a `CallTarget` index and the `procEntries` table it is
read from come from the same `SlotProgram`, and nothing rebuilds one
without the other; `callProcAt` still reports a miss rather than
projecting a partial record. An opaque `IdExpr`/`ValExpr` constructor
that can only be made by the binder would close the third; a typed
`HostCallRef` issued by the registry would close the fourth.

### Panics this catalogue missed

A re-grep of `error` at the current revision turns up sites the
original audit did not list. None is known-reachable from a
well-formed program, but the inventory above is therefore not
exhaustive:

| Site                                                     | Kind                                        |
|----------------------------------------------------------|---------------------------------------------|
| `src/YCHR/Internal/Runtime/Interpreter.hs:547` (`activateSuspensionId`) | leading-id shape check |
| `src/YCHR/Run.hs:616` (`executeBodyGoal`, `BodyOr`)       | query disjunction should have been rejected (YCHR-30006) |
| `src/YCHR/Internal/Compile.hs:1220` (`compileBodyGoal`, `BodyOr`) | `lowerDisjunctions` should have run first |
| `src/YCHR/Internal/Desugar.hs:999` (`ruleModName`)        | non-empty head                             |
| `src/YCHR/Internal/Desugar/Disjunction.hs:103,209`        | lifted rule is a simplification; non-empty head |
| `src/YCHR/Internal/Backend/Scheme.hs:231` (`programInfoBindingName`) | non-empty library name          |
| `src/YCHR/Internal/Resolve.hs:1438` (`parseFlatName`)     | renamer post-condition: flat name contains `':'` |
| `src/YCHR/Internal/TypeCheck.hs:404` (`malformed`)        | solver returned a shape the decoder does not know |
| `src/YCHR/Internal/TypeCheck/Encode.hs:403,407` (`encodedToValue`) | encoded term is ground (no `Wildcard` / `VarTerm`) |
| `src/YCHR/Internal/Resources.hs:138` (`compileChecker`)   | bundled type-checker sources failed to compile |
| `src/YCHR/DSL.hs:373` (`termToConstraint`)                | DSL combinator given a non-compound `Term` |
| `src/ghc/YCHR/Convert/Generic.hs:120`                     | `undefined :: M1 C c f p` passed to `conName` to read a constructor name |
| `embed/YCHR/Embedded/Generate/Code.hs:76`                 | non-finite `Double` in generated code       |
| `embed/YCHR/Embedded/Generate/ToCode.hs:89,108`           | `V1` value; defining module missing from the alias table |
| `embed/YCHR/Embedded.hs:48,58`                            | embedded stdlib / type-checker failed to parse or compile |

The two `BodyOr` sites are phase invariants of the same family as
the `LambdaExpr` case below: the constructor survives in the type and
each pass asserts it was already lowered. A phase index on
`Desugared.BodyGoal` (or a post-lowering type without `BodyOr`) would
discharge both. The three `Meta.hs` host-call sites
(`write_term_to_string`, `read_term_from_string`) are closed: an arity
or parse failure now raises `runtimeErrorS` rather than `error`, so it
is a structured runtime error rather than a plain `ErrorCall` that
`invokeHostCall`'s `try @SomeException` happens to catch.

Deliberately partial, and not to be "fixed": `Data.Text.Shim.breakOn`
and `Data.Text.Shim.last` (`src/Data/Text/Shim.hs:39,71`) raise exactly
where `Data.Text` raises, so the shim stays a drop-in replacement.
Totalising them would silently diverge from the API they stand in for.

### `R.LambdaExpr` survives lambda lifting — `src/YCHR/Run.hs:757`, `src/YCHR/Internal/Compile.hs:806`, `src/YCHR/Internal/Backend/SchemeDriver.hs:190`

```haskell
-- Run.hs
evalNestedExpr (R.LambdaExpr _ _) =
  error "Run.evalNestedExpr: LambdaExpr survived lambda lifting"
-- Compile.hs
R.LambdaExpr {} ->
  error "Compile.compileExpr: LambdaExpr survived lambda lifting"
-- SchemeDriver.hs (goal-argument path)
exprToScheme (R.LambdaExpr _ _) =
  error "SchemeDriver.exprToScheme: goal lambda not rejected by generateDriver"
```

`Desugar.liftAllLambdas` is documented (see the `LambdaExpr` haddock in
`src/YCHR/Internal/Resolved.hs`) to rewrite every `R.LambdaExpr` into a
`__closure`-headed `R.CtorExpr` before Compile/Run run. The IR type
still carries the constructor, so each consumer keeps a defensive
`error`. A separate post-lifting expression type (or a phase index,
e.g. `Expr 'PreLift` / `Expr 'PostLift`) with no `LambdaExpr`
constructor would turn all three runtime crashes into compile errors.
The Scheme driver site is a slightly different concern: goal-argument
expressions never reach `liftAllLambdas` at all, so it is not a
survived-lifting case but a genuine backend gap. It is now guarded by
`generateDriver`'s `LambdasInSchemeDriver` check (see "Already
closed"), which makes it unreachable; the same type-level fix would
retire the guard by making "lambdas in goal arguments" representable
separately.


## 2. Data types that admit invalid states

### `VarState` orphans — `src/YCHR/Internal/Runtime/Types.hs:43-48`

```haskell
data VarState = Unbound !VarId ![SuspensionId] | Bound !Value
```

The invariant is "binding a variable emits (or transfers) its
observer list before the cell becomes `Bound`". An earlier revision of
this entry framed it as "a `Bound` value can carry a stale observer
list". That is **not representable**: `Bound !Value` has no list slot,
so the data shape already rules out the stated hazard. What remains is
a control-flow obligation — `unify'` must go through the observer
emit/transfer path (`Var.hs:162-195`) and not blind-write
`Bound` — and the suggested constructor-hiding accessor module would
not encode it either: hiding the constructors centralizes the write
but still permits `writeVarState var (Bound v)` with `obs`
discarded.

The real defence is already in place and structural: `withUnboundVar`
(`Var.hs:123-133`) means every reader of the cell that needs its
contents goes through a continuation that is *given* the observers,
so there is no arm in which they can be silently dropped. Treat this
entry as narrowed to "the drain/transfer discipline is a `Var.hs`
convention, not a type", and do not expect a cheap type fix.

### Compiler IR carries unchecked arity fields — `src/YCHR/Internal/Compile/Types.hs`

- `Partner { constraint :: HeadConstraint }` — note the type is
  `HeadConstraint`, not `QualifiedConstraint` (that narrowing is the
  same HNF change). `length constraint.args` is assumed to match the
  symbol table's recorded arity; not cross-checked. Harder to encode
  here than the (now deleted) `Occurrence.conArity`, because the
  symbol-table arity is not a field of `Partner` and `cType` is
  already the resolved form.

- `IndexCondition { argIndex :: ArgIndex, ... }` — `argIndex` is not
  bounds-checked against the partner's arity at construction. The
  compiler trusts itself, but the trust is currently *justified*: see
  the `classifyEqual` entry in §4 — the only producer enumerates the
  partner's argument positions, so no out-of-range value can be built
  today. Encoding it would be belt-and-braces rather than closing a
  live hole.

A common fix for these two: make arity a `newtype` and have a smart
constructor for `Partner`/`IndexCondition` that reconciles or rejects
mismatches.

### Import-placement checking fails open on a missing `trailingLoc` key — `src/YCHR/Internal/Rename.hs:274`, `:532`

```haskell
-- RenameInputs
trailingLoc :: Map Text (Maybe SourceLoc)
-- RenameCtx
currentTrailingLoc = Map.findWithDefault Nothing m.name inputs.trailingLoc
```

`checkPlacement` (`Rename.hs:671-676`) emits `UseModuleOutOfOrder`
(YCHR-20007) only when the lookup yields `Just`. The map has to
distinguish three states and has room for two: a module exempt from the
check (bundled libraries, absent from `trailingLoc` but present in
`allMods`), a user module with no non-import directive (`Parser.hs:357`
records `Nothing`), and a caller that forgot the module. The third reads
as the first, so the diagnostic silently disappears.

No live hole today: `compileModules` keys the map by every parsed user
header (`Pipeline.hs:300-301`), and the empty-map paths —
`compileParsedModules` (`Pipeline.hs:338`) and query renaming
(`defaultRenameInputs`) — are deliberate, because programmatically built
input has no source order to violate (`Pipeline.hs:312-316`). The
exposure is a future caller or path that omits a module. The record's
two fields also disagree on what a missing key means: the sibling
`operatorExports :: Map Text [OpDecl]` (`Rename.hs:270`) already uses
plain absence as a valid state.

Fix: encode "exempt" instead of overloading absence —
`data Placement = Checked SourceLoc | Exempt` with
`trailingLoc :: Map Text Placement`. A missing key then means only
"caller forgot" and can be reported. A `RenameInputs` smart constructor
that cross-checks the key set against the module list would catch it
with no type change.


## 3. Documented invariants worth promoting into types

### Occurrence numbering is 1-based — `src/YCHR/Internal/Compile/Occurrences.hs:83`

```haskell
assignNumbers = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..]
```

Paper §ωr requires 1-based numbering. The `OccurrenceNumber` newtype
is unconstrained; a smart constructor `mkOccurrenceNumber :: Int ->
Maybe OccurrenceNumber` (or starting from `1` only) would enforce it.
Note that the real defect here is not `assignNumbers` but the
`OccurrenceNumber 0` an `Occurrence` is born with in `mkOccurrence`
(`Occurrences.hs:170`) — a placeholder that is always overwritten
moments later, and the only value a 1-based smart constructor would
have to reject. Low value; deferred. The structural alternative is a
`NumberedOccurrence` wrapper (an unnumbered `Occurrence` becomes a
numbered one in the pass), which removes the placeholder instead of
validating it, at the cost of touching the three `number` readers
(`Compile.hs:325`, `Occurrences.hs:83`, `Names.hs:205-208`).

### `tc_unify` argument order — `typechecker/solver.chr`

Source-variable types must be on the left of `tc_unify` and declared
types on the right. Every rule has an explicit mirror, so the *verdict*
does not depend on the order; what does is `tc_unify_error`'s
`tpair(T1, T2)`, i.e. which of the two types the message presents as
the one required and which as the one found. A swapped call renders
backwards. Today this is enforced by routing every cross-comparison
through named helpers (`check_constraint_use`, `check_function_use`,
`check_constructor_use`), which put the operands in place themselves.
Two distinct `ty`-like types — one for each side — would make an
emitter's call total, at the cost of a conversion at every helper.

## 4. Undocumented invariants the implementation relies on

### `$call/N` supports N ∈ {1, …, 10}, enforced at resolution — `src/YCHR/Internal/Resolved.hs`

`maxCallArity = 10` in `YCHR.Internal.Resolved` is the single source of
truth for the supported dynamic-call arity. `Resolve.termToExpr`
rejects a surface `'$call'` outside that range — including zero, i.e.
`'$call'(F)` and a bare `'$call'` — with `UnsupportedCallArity`
(YCHR-16022) while it recognizes the `'$call'` shape.

Resolving rather than compiling is what makes the check total: programs,
queries and generated drivers all reach the compiler only through
`Resolve.termToExpr`, so an out-of-range arity cannot reach the backend.
The limit is now a property of the surface language rather than of the
compiler's shape: it used to be forced by the one-dispatcher-per-arity
code generator (`genCallFunDispatches`), which keyed `'$call'` dispatch
has removed. The compiler's `ApplyClosure` sites are arity-generic and
would work at any arity; the cap is kept deliberately, aligned with the
prelude's `call/N` wrapper family, and lifting it would be a separate
language change with its own documentation and tests.

This replaced a silent gap: `$call/3` … `$call/10` used to compile to a
`call_N` name with no procedure and fail at runtime, and `$call/11`+
did the same. The §5 procedure-name closure check remains worthwhile for
the rest of the `CallExpr` namespace, but there is no longer a `$call`
arity cap for it to subsume.

### `partArity` derived from desugared head matches runtime constraint shape — `src/YCHR/Internal/Compile.hs:454`

```haskell
partArity = length partner.constraint.args
```

`partArity` is used to generate `FieldArg` indices into the partner
suspension. The compiler assumes the symbol-table arity for that
constraint type matches the desugared-head arity; a mismatch would
make the runtime access out-of-bounds fields. This used to compound
with the `ConstraintType (-1)` placeholder, which is now gone (see
"Already closed"): a symbol-table miss drops the occurrence instead
of producing one with a bogus type, so the remaining exposure is a
genuine arity *disagreement* between the symbol table and the
desugared head, not a lookup failure.

### `classifyEqual` / `IndexCondition` — the bounds worry is overstated — `src/YCHR/Internal/Compile.hs:820-832`

The earlier statement of this entry ("`asPartnerArg` produces an
`(ArgIndex, …)` pair that is baked into an `IndexCondition` without
any bounds check") is technically true of the type but overstates the
exposure. `asPartnerArg` (`Compile.hs:803-812`) *generates* the index
by enumerating the partner's argument positions:

```haskell
j <- [0 .. length p.constraint.args - 1]
```

so every `ArgIndex` it can return is in `[0, arity-1]` by
construction, and it is the only producer `classifyEqual` uses. There
is no live path to an out-of-range `IndexCondition.argIndex`. The
tighter type (a smart constructor that takes the partner's arity)
would be belt-and-braces; it is not worth ranking with the §2 items.
The same enumeration pattern makes `wrapInPartnerLoops`'s `FieldArg`
indices (`Compile.hs:460-464`) in range by construction.

### `History` keys assume canonical `SuspensionId` ordering — `src/YCHR/Internal/Runtime/History.hs:22-32`

History is keyed by `(RuleId, [SuspensionId])`. Equality is on the
list shape; the caller must build the list in a canonical order at
every call site.

**The order is semantically load-bearing — do not replace the list
with a `Set`, and do not sort by id.** The list is a
head-position-indexed *tuple*: for `leq(X,Y), leq(Y,Z) ==> leq(X,Z)`
the matches `(c1,c2)` and `(c2,c1)` are two distinct firings and both
must happen. A set (or an id-sorted list) collapses them into one key
and silently suppresses the second — a wrong-answer bug, not a
performance one. `test/YCHR/Runtime/HistoryTest.hs` pins the
order-sensitive behaviour.

What the caller actually owes is weaker: every occurrence procedure
of the same rule must spell the same match with the ids in the same
*head-position* order, so that a match reached from a different
active occurrence keys to the same entry. That half is now encoded on
the compiler side by `VM.Types.HistoryIds` (see "Already closed");
the runtime key stays `(RuleId, [SuspensionId])`, unchanged.

### Symbol-table lookup for unknown constructor falls through to `any` — `typechecker/walk.chr` (`idx_within`)

```
idx_within(_, nothing) -> true.
idx_within(Idx, just(Info)) -> Idx < con_arity(Info).
```

An unknown constructor answers `true`, so the extraction is emitted
anyway and the solver's `unknown_guard_getarg` unifies the result with
`ty_any` — which, under the no-bind rule for `any`, leaves a flexible
slot flexible rather than typing it. An out-of-range index on a *known*
constructor is skipped
silently on the assumption that the constructor-arity walk
(`pure.chr`) reported it. Neither coupling is visible in the types:
a `known_con` / `unknown_con` split, or an invariant on constructor-map
membership, would make it explicit.

### Rule-guard residuals do not tell — `src/YCHR/Internal/Compile.hs:371-384, 840` (`residualCheck`, `genGuardedFire`)

The `BoolExpr` a rule guard compiles to is a `BAnd` chain of `BEqual`
(ask) conjuncts and `BFromVal (EvalDeep …)` calls into user code.
Nothing in the type stops a `BUnify` — or a `Store`/`Kill`/
`AddHistory` reached through a called procedure — from appearing
there; only the way `residualCheck` is built, and the fact that a
compiled function body has no tell forms, keeps it out.

This used to be a correctness nicety ("guards must not leave
half-done bindings when they fail"). It is now load-bearing twice
over. First, `genGuardedFire` wraps the residual in `BSoftGuard`,
which abandons a partly-evaluated guard on an instantiation error and
continues with `False`. If the residual could tell, the abandoned
prefix would leave store, history or reactivation-queue state behind
with nothing to roll it back. Second, Late Storage leaves the active
constraint alive-but-unstored throughout guard evaluation and partner
search: sound only because no in-session `BUnify` can run in that
window, so there is no reactivation event for the unobserved
constraint to miss and no nested activation that could need it as a
partner before it is stored. Note the guarantee is about *mutation*:
the store can still be read in that window — a guard reaching
`write_store_to_list` / `print_store` through a host call will not
list the alive-but-unstored active constraint, where eager storage
would have. Nothing in the corpus exercises this; it is the one
observable divergence Late Storage introduces.

**Scope, precisely.** The guarantee covers the runtime's own
bookkeeping — constraint store, propagation history, reactivation
queue, call stack, trace depth — and it is what the catch depends on.
It does *not* extend to a `HostCall` in the guard. A host function
receives the session and can bind shared logical-variable cells;
`run_chr_session/1` (`src/YCHR/Internal/Runtime/Search.hs`)
documents doing exactly that as its result channel. Such a binding
survives whether the guard is abandoned by `BSoftGuard` or simply
evaluates to `False` on its own, so the catch adds no exposure the
language did not already have — but "a guard cannot mutate anything"
is not a true statement of the invariant, and must not be relied on as
one.

A separate `GuardExpr` type (a `BoolExpr` subset with no `BUnify` and
only calls into a guard-safe procedure set) would encode the compiled
half; the host-call half would need a purity tag on
`HostCallFn`. Short of either, `Note [Soft guard catch safety]` in the
interpreter records what the catch depends on.


## 5. Cross-cutting compiler ↔ runtime contracts

These span the compiler/runtime boundary. The compiler emits one
shape, the runtime consumes another; nothing on either side checks
that they agree.

### Closed procedure-name set

Closed for compiler output. Every `CallExpr` name (`tell_<c>/<n>`,
`activate_<c>/<n>`, `occurrence_<c>_<n>_<j>`, `func_<…>`,
`reactivate_dispatch`) must exist in the generated procedure table. The
interpreter still errors at runtime if a name it is handed is missing, but
compiler output can no longer reach that error:
`YCHR.Internal.VM.Closure.danglingTargets` checks every `CallExpr` name,
and every target of the program's `evaluables` and `callables` tables,
against the program's own procedures; `Compile.Pipeline.compileModules`
asserts it with an internal `error` (a miss is a compiler bug, not user
input, so it is not given a diagnostic code), and a test in
`test/YCHR/VM/ClosureTest.hs` pins the checker's own behaviour.

The union caveat is handled where the item said it must be. Query-time
procedures and callables are compiled after the program and merged in by
`Session.withCHRExtra`, so that is where they are checked, against the
union of the compiled names and their own (`extraClosureFailure`); the
check short-circuits when a query adds neither, which is every query that
does not lift a lambda. What remains a runtime error is the hand-built
`Program` the interpreter's `interpret` entry accepts — that is not
compiler output, and `test/YCHR/Runtime/InterpreterTest.hs` pins the
`unknown procedure` message it produces.

The check is not free: it walks the program once per compile, which on
MicroHs is 3.7 M reductions on `compile -t vm typechecker/*.chr` (+0.7 %)
and 1.0 M on `repl --quiet` startup. The measurements are in
`MICROHS_PERFORMANCE.md` §7C.1, which is also where the alternative —
keeping the checker as a test only — is weighed.

### `reactivate_dispatch` covers every constraint type

Every `Unify`/body emits `DrainReactivationQueue → CallExpr
reactivate_dispatch`. The dispatch arms must list every constraint
type. If one is missed, reactivation of that type is a silent no-op
rather than an error. A typed dispatch table (parameterised by the
`ConstraintType` set) would close it.

### `tell_<c>/N` must exist for every constraint a query can ask for

`Session.tellConstraint` (`src/YCHR/Internal/Runtime/Session.hs:223-229`)
resolves a name and arity through the export map and calls
`tellProcName resolved arity`. The compiler must have generated
exactly that procedure. `tellConstraint` does check the procedure map
and raises a runtime error on a miss, so this is not a silent
failure — but it surfaces at query time, not compile time.

### `Store` reaches every surviving suspension

Under Late Storage, `Store` no longer follows `CreateConstraint`
directly: the compiler emits it before a non-empty kept-active rule
body and at the end of `activate_c`, and `storeConstraint` is
idempotent (a `stored` flag gates the append and the observer
registration). What the IR structure now guarantees — without
encoding it — is that every suspension still alive when its
activation returns has passed through a `Store`. A compiler output
that dropped the end-of-activate `Store` would leave a live
constraint invisible to `Foreach` and unobserved by reactivation,
silently.

### Store index agrees with the store it describes — `src/YCHR/Internal/Runtime/Store.hs`

The store's per-argument indexes (`YCHR.Internal.Runtime.Index`, the
paper's *Indexing* optimization, fed by
`YCHR.Internal.VM.Index.indexablePositions`) are a /narrowing/ of what
`Foreach` would otherwise scan, so four couplings are load-bearing and
none is encoded:

- **Every append to `storeByType` records its index entries, and only
  `storeConstraint` appends.** `candidateSuspensions` answers from the
  index whenever it has one for the type — its fallback is the *whole
  bucket*, never an empty answer from an index that was not built — so
  a path that appended without recording would make a stored suspension
  *invisible* to every indexed lookup. Today the only `Seq.|>` on a type
  bucket is in `storeConstraint`, and the index is written there, on the
  same first-store branch as the `stored` flag.
- **The index is consulted only for a `(type, position)` pair
  `indexablePositions` reports.** A position the store was never told
  to index has no entries, so asking for it would answer `IntSet.empty`
  — every candidate lost — rather than the scan it deserves. The
  interpreter asks `indexedPositionsFor`, which answers for exactly the
  positions a *currently indexed* type has.
- **The index is restored by the same snapshot as the store.**
  `StoreSnapshot` carries both, and `forkSearchSessionEnv` starts both
  empty; restoring one without the other would leave the iterator
  answering from slots the restored store does not have (or missing
  entries for the suspensions it does have). Both are persistent values
  behind one `IORef` each, so the undo stays a pointer write and the
  undo trail never sees them.
- **A type is indexed from the store that crosses `indexThreshold`, and
  that store files the whole bucket.** On-demand indexing means a type
  can be unindexed while it already holds suspensions, so the crossing
  store must file them from the bucket rather than from a
  per-store record it does not have — and a lookup whose type is not
  indexed (`typeIndexed` is false) must scan, not read the empty index.
  Getting the first wrong leaves every suspension stored below the
  threshold unfindable; getting the second wrong loses every candidate.

What is *deliberately* not trimmed: a kill leaves the index entry in
place (the iterator's liveness check filters it, exactly as it does for
a scan), and a suspension whose indexed argument was not fully ground
when it was stored stays in the fallback set for good even after that
argument is bound. Both cost memory, never correctness, and both keep
the index append-only — which is what makes it cheap enough to be worth
having.

### Scheme store index agrees with the store it describes — `scheme/ychr/store.sls`

The same optimization, with the same couplings, in the Scheme runtime.
The index is session state — `session-index-positions` (the positions the
generated `Foreach` loops may be answered for, emitted by the compiler)
and `session-store-index` (the index itself) — so the four couplings that
matter are:

- **Every append to a type's growable records its index entries, and only
  `store-constraint` appends.** `candidate-suspensions` answers from the
  index whenever the type has one — its fallback is the *whole bucket*,
  never an empty answer from an index that was not built — so a path that
  pushed without filing would make a stored suspension *invisible* to
  every indexed lookup.
- **A lookup is only made for a position `indexed-positions-for`
  reports.** That is exactly a position in
  `session-index-positions` of a type whose `session-store-index` entry
  is set. Asking for a position of an unindexed type would answer the
  empty candidate set, not the scan it deserves.
- **A type is indexed from the store that crosses `index-threshold`, and
  that store files the whole existing bucket.** On-demand indexing means
  a type can hold suspensions while unindexed, so the crossing store must
  file them from the growable (`file-backlog!`); a lookup whose type is
  not indexed yet must scan, not read the empty index.
- **The index is state of *this* session and has no snapshot or undo
  counterpart, because the Scheme runtime has no search driver.** Unlike
  the Haskell runtime, there is nothing to restore it from, so nothing
  keeps it in step with a fork. A future search driver
  (`dev-docs/SCHEME_BACKEND_GAPS.md`, `library(search)`) must capture and
  restore it together with the store and the history, or a branch will
  answer from slots the restored store no longer has.

What is deliberately not trimmed is the same as on the Haskell side: a
kill leaves the bucket entry in place (the iterator's liveness check
filters it, exactly as for a scan), and a suspension whose indexed
argument was not fully ground when it was stored stays in the position's
fallback list for good. Both cost memory, never correctness.

Key equality is the other half, and it is defended in
`scheme/ychr/var.sls`: a key must never be finer than ask-equality
(`equal?/chr`), or a lookup would drop a candidate. Numbers are
normalized (`number-key`): `0.0` and `-0.0` share a key although `eqv?`
distinguishes them, and every NaN shares one. Terms are keyed
structurally, functor plus one key per argument — never by object
identity, which is what `equal?` would do for a record. The key walk is
also total: it must never raise where the old scan answered, so its
NaN test is guarded by `flonum?` (`nan?` raises on a non-real complex,
which `eqv?` compares happily) and every value `equal?/chr` cannot
equate simply has no key and lands in the fallback set.

### Session construction — `src/YCHR/Internal/Runtime/Session.hs:122-151`

This entry described a layered effect stack (`runCHR` building
Unify → CHRStore → PropHistory → ReactQueue → Writer → CallStack →
CHR) that no longer exists: `Chr` is a `ReaderT SessionEnv IO`, and
`initSessionEnv` allocates every piece of session state into one
record. The ordering invariant went away with the stack.

What is left is weaker and lives in `withCHRExtra`: the procedure map is
`addProcedures si.slotProgram extraProcs`, i.e. query-time procedures
deliberately *shadow* compiled ones on a name collision. The merged map
is left-biased, so swapping the operands silently reverses that. Nothing
but the argument order says which side wins. Extras are lowered by
`addProcedures` before the merge, so every entry in the map is in the
same phase as the compiled ones.

One asymmetry is newer than the rest and is worth stating: a *resolved*
call does not see that shadowing. A compiled procedure's calls were
resolved against the compiled program's own procedures when it was
lowered, so an extra that shadows a compiled name is reached by
host-initiated calls (a query's `tell_<c>`, `'$call'`, `is`) but not by a
compiled call to that name. Nothing observable depends on this today:
extras are lifted lambdas with fresh `__lambda_N` names and cannot
collide, which is the same reason the merge order is only a convention.
It would matter to a future feature that genuinely overrode a compiled
procedure at query time.

### The interpreter's slot phase mirrors the VM AST — `src/YCHR/Internal/Interpreter/Slots.hs`

The Haskell interpreter does not run the VM AST. It runs a second,
interpreter-owned AST in which every local variable is a per-procedure
integer slot (`YCHR.Internal.Interpreter.Slots`), produced once at
compilation and carried on `CompiledProgram.slotProgram`. Two
invariants make that duplication safe, and neither is encoded in a
type:

- **The phase is total and structure-preserving.** Every VM `Stmt`,
  `ValExpr`, `BoolExpr`, `IdExpr` and `CallArg` constructor has exactly
  one counterpart, and the lowering only rewrites the local-variable
  slots and a call's callee. A VM constructor added without its
  counterpart makes the lowering's pattern matches non-exhaustive, which
  is a compile error under `-Wall -Werror`; that is the mechanism that
  keeps the phase from going silently stale.
  `test/YCHR/Interpreter/SlotsTest.hs` pins the slot numbering the
  interpreter depends on.
- **A call target and the procedure table it is read from come from the
  same `SlotProgram`.** `lowerProgram` resolves each `CallExpr` name to
  the callee's `ProcIx` (its position in the program's procedure list)
  and stores the procedures in `slotProcEntries` keyed by that same
  index; `addProcedures` extends both together when query-time lambdas
  arrive. The interpreter therefore reads a `ProcIndex` target out of
  `SessionEnv.procEntries` with no lookup by name, and a miss is
  impossible by construction rather than by convention. A name the
  program does not declare stays a `ProcName` target and reaches the
  interpreter's existing "unknown procedure" error; compiler output
  cannot produce one (§5, "Closed procedure-name set").
- **A slot is read from the map its kind binds it in, and a name the
  phase never saw in scope lowers to a slot nothing binds.** Slots are
  numbered from one counter per procedure, shared by both kinds,
  because a parameter is heterogeneous at run time: `bindParams` binds
  by the runtime tag of the argument it is handed, so parameter *i*
  must be slot *i* whether the value lands in `envValues` or `envIds`.
  The IR guarantees a name is bound in only one of the two maps; the
  interpreter therefore reads a value reference (`SVar`) from
  `envValues` and an id reference (`SIdVar`) from `envIds`, and a
  reference with no binder in scope reaches the existing "unbound
  variable" runtime error rather than a wrong slot.

What is deliberately *not* an invariant: that a binder's slot matches a
particular lexical scope. The interpreter's environment is one mutable
map per call, so a binding made inside an `If` branch is visible after
it and a `Foreach` body sees the bindings made earlier in the same
body; the lowering walks the body left to right and allocates a fresh
slot per binder.

Two properties of emitted code are what make that reading sound, and
both are assumptions on the compiler rather than consequences of the
walk:

- **Every read is preceded on its execution path by the binder the walk
  selected for it.** Names are *not* unique within a procedure —
  `genActivate` emits one `LetVal "dropped"` per occurrence, and an
  equation chain binds the same pattern variable once per equation — but
  each read sits in the segment that follows its own binder, so the
  fresh slot is the one that read should see. A read textually before
  its binder in a loop body relies on the flat map surviving an earlier
  iteration, and would resolve to the slot that binder takes, which is
  what the flat map would have read too.
- **No emitted `If` binds a name in its else arm.** The then arm carries
  the rule body or the equation and the else arm is either empty or
  `inconclusiveElse`, which only `AssignVal`s a binder introduced
  outside the `If`. A hand-built program that bound one name in *both*
  arms and read it after the `If` would see the walk resolve that read
  to the else arm's slot, so a then-arm execution would leave it unbound
  where the flat map succeeded.

The second is pinned by a case in `test/YCHR/Interpreter/SlotsTest.hs`, so a
change to the reading has to be deliberate.

### Scheme runtime ABI

`src/YCHR/Internal/Backend/Scheme.hs` bakes in many assumptions the Scheme
runtime must satisfy: the `(ychr runtime)` library is imported, every
procedure takes `%s` as its first parameter, a procedure whose `Return`s
can only leave it from tail position compiles to a plain value-producing
expression while a procedure with a `Return` trapped in a `Foreach` or
`DrainReactivationQueue` body uses `call/cc` with `%return`, `Break` and
`Continue` use a `call/cc` at the loop that owns the label (and only when
the body names it), the session thunk exported by each generated library
calls `(%make-session N POSITIONS TABLE)` directly, where `TABLE` is the
program's operator table as a `make-op-table` literal over
`(FIXITY TYPE "name")` entries and `POSITIONS`/`TABLE` default to the
unindexed store and `builtin-op-table` in the shorter clauses,
`drain-queue!` takes
`(session, alive-checking-lambda)`, `Foreach` expects
`(snapshot, count)` from the runtime. (The binding printer's operator
table is the fixed `Pretty.prettyOps` — built-ins plus arithmetic — not
the session's, so a user-declared operator still prints as a compound.)
One more assumption rides on the
tail compilation: an `If` whose arm contains a `Return` is emitted as
`(if c ARM-spliced-before-rest ARM-spliced-before-rest)`, so a binder an
arm introduces lexically scopes over the statements that follow the
`If`. That matches the interpreter's flat mutable `Env` (`LetVal` and
`AssignVal` both just insert), and it is sound for the same reason the
interpreter's slot walk is — no emitted `If` leaves a name in `rest`
that an arm bound (see "Two properties of emitted code are what make
that reading sound" above). These contracts live only in code, on both
sides. The surface is now written down in `SCHEME_BACKEND_GAPS.md`'s
*Scheme runtime ABI* section, which closes the documentation half of
this entry; encoding it in types remains harder because it crosses a
host-language boundary.


## 6. Clean-up ideas (not invariants)

Duplications and structural improvements that no invariant depends on,
recorded so they do not have to live in review comments. Line numbers
are from the style pass that added this section.

### Function visibility is computed twice

`buildVisibleFunctionNames` (`Rename.hs:1239`, name-keyed, per module)
and `buildFunctionVisibility` (`Resolve.hs:326`, `(name, arity)`-keyed,
whole program) both decide what a module can see. They agree today —
the renamer says so at `Rename.hs:1236` — but only by hand. Unifying on
the resolver's representation, or one shared helper, would make the
agreement structural.

### `TypeCheck.decodeError` is a long hand-written case

`TypeCheck.hs:275-342` has one `case` arm per diagnostic code; a
`(code, arity, constructor)` table would be shorter and could be shared
with `decodeWarning` (`:360`).

### `TypeCheck/Render.hs` fallbacks can hide encoding drift

`Render.hs:75,83,99` render `"(?)"`, `"fun(?) -> "` and `"?"` for an
unexpected solver value. Readable, but it also swallows encoding drift;
asserting, or routing through `malformed`, would surface it earlier.
A deliberate trade today: "decide and document", not a clear bug.

### Unqualified imports of utility-module helpers

`STYLE.md` asks for qualified imports of container/utility modules. The
codebase does so for `Data.Text`/`Set`/`Map`, but open-imports small
helpers from `Data.List`/`Data.Maybe`/`Data.Char` (e.g.
`SchemeDriver.hs:15`). Needs a repo-wide decision plus a mechanical
rewrite; changing one module alone would be worse than leaving it.

### Naked scalars and domain tuples

`STYLE.md`'s "Named, unique data types" and records-over-tuples rules
have not had a codebase-wide audit. Look for a bare `Text`/`Int` used
as an identifier where a `newtype` would name the slot, a tuple used as
a domain value in a record or API rather than a local zip, and a `Bool`
field carrying a convention a sum type could carry. A modelling pass,
not a mechanical edit; it would change exported signatures.

### Accepted long literals (do not shorten)

`STYLE.md` allows a line over 90 characters only for an unsplittable
literal. The style pass left six: the README URL at `src/YCHR.hs:14`,
an error-message literal at `src/YCHR/Internal/Meta.hs:233`, and four
`testCase` names in `test/YCHR/RenameTest.hs` (951, 982, 1270, 1321).
Shortening any of them would change either a URL or a test name.

## Suggested next targets

If you want a roughly-ordered list of the most actionable wins:

1. ~~**Procedure-name closure check** (§5).~~ Done: every `CallExpr` name
   and both dispatch tables are checked against the procedure table, over
   the compiled program and over the query-time extras against the
   unioned map. See §5 "Closed procedure-name set" and
   `MICROHS_PERFORMANCE.md` §7C.1 for what the walk costs.
2. **Phase-indexed `Expr`** (§1, `R.LambdaExpr`; and the two `BodyOr`
   sites in "Panics this catalogue missed"). The larger
   follow-up: a trees-that-grow field on `LambdaExpr` (or an `Expr
   'PreLift` / `Expr 'PostLift` index) removes the constructor after
   lifting, closing all three `LambdaExpr` panics at once and
   retiring `generateDriver`'s guard in favour of a type. A
   `BodyGoal 'PreLower` / `'PostLower` index would do the same for
   `Run.executeBodyGoal` and `Compile.compileBodyGoal`.

### Considered and deliberately not done

- **`SuspensionId` opacity** (§1's `lookupSusp`). Making the id an
  opaque handle issuable only by `createConstraint` would be a false
  guarantee: sub-sessions legitimately carry *foreign* ids. A
  variable's observer list can name suspensions belonging to another
  session, and `Reactivation.enqueueObservers` filters them out —
  along with the ids of constraints that have since been killed, which
  an observer list also never sheds. An id being well-formed says nothing
  about it being resolvable *here*. A real fix needs session-scoped
  phantom tags, not plain opacity.
- **A `Set`-keyed propagation history** (§4). Wrong — it would
  suppress firings. See that entry.
