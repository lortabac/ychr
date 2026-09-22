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
  `envValues :: Map Name Value` and `envIds :: Map Name SuspensionId`.
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
  order-insensitive — `buildEvaluables` keys by name,
  `genCallFunDispatches` arms are mutually exclusive, and
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
  `__lambda_N` procedure nor extend that library's `call_N` dispatch
  chain to reach it. `exprToScheme`'s lambda arm remains an `error`,
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


## 1. `error` / `runtimeErrorS` for "can't happen" cases

Each of these crashes if the documented runtime invariant is violated.
A stronger type or a checked smart constructor would turn the runtime
panic into a compile-time error.

### `getArg` operand and bounds — `src/YCHR/Internal/Runtime/Var.hs:359-360`

```haskell
| otherwise -> error $ "getArg: index " ++ show idx ++ " out of bounds"
_ -> error "getArg: not a compound term"
```

`getArg` is partial on shape (must be `VTerm`) and on index. Callers
guarantee both, but neither is enforced. A typed term-projection API
keyed on a verified `(VTerm functor arity)` handle would close it.

### `lookupSusp` — `src/YCHR/Internal/Runtime/Store.hs:61`

```haskell
Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid
```

Every `SuspensionId` in circulation must have been allocated by
`createConstraint`. The header comment calls a miss "a runtime
invariant violation, not a user-facing failure" — exactly the case for
a typed handle (e.g. an opaque newtype that can only be created by the
allocation API).

### `getConstraintArg` bounds — `src/YCHR/Internal/Runtime/Store.hs:140`

```haskell
else error $ "getConstraintArg: index " ++ show idx ++ " out of bounds"
```

Same shape as `getArg`. The compiler is responsible for emitting only
in-range `ArgIndex` values; a smart-constructor for `ArgIndex` keyed
on the constraint type's arity (or a `Vector` of fixed length in the
suspension) would push the check up.

### Remaining interpreter shape checks — `src/YCHR/Internal/Runtime/Interpreter.hs`

After the value-vs-id and bool splits, three sites remain that are
name-resolution invariants rather than shape invariants:

| Site                                | Required precondition          |
|-------------------------------------|--------------------------------|
| `callProc` (unknown name), `:397`   | name resolves in `procMap`     |
| `evalValExpr (Var name)`, `:677`    | name in `envValues`            |
| `invokeHostCall` (unknown), `:871`  | name in registry               |

Closure checks at compile time (see §5 "Closed procedure-name set")
would close the first; an opaque `IdExpr`/`ValExpr` constructor that
can only be made by the binder would close the second; a typed
`HostCallRef` issued by the registry would close the third.

### Panics this catalogue missed

A re-grep of `error` at the current revision turns up sites the
original audit did not list. None is known-reachable from a
well-formed program, but the inventory above is therefore not
exhaustive:

| Site                                                     | Kind                                        |
|----------------------------------------------------------|---------------------------------------------|
| `src/YCHR/Internal/Runtime/Interpreter.hs:496` (`activateSuspensionId`) | leading-id shape check |
| `src/YCHR/Run.hs:548` (`executeBodyGoal`, `BodyOr`)       | query disjunction should have been rejected (YCHR-30006) |
| `src/YCHR/Internal/Compile.hs:1122` (`compileBodyGoal`, `BodyOr`) | `lowerDisjunctions` should have run first |
| `src/YCHR/Internal/Desugar.hs:987` (`ruleModName`)        | non-empty head                             |
| `src/YCHR/Internal/Desugar/Disjunction.hs:101,206`        | lifted rule is a simplification; non-empty head |
| `src/YCHR/Internal/Backend/Scheme.hs:214` (`programInfoBindingName`) | non-empty library name          |
| `src/YCHR/Internal/Meta.hs:184,190,192`                   | host-call arity / parse result (`write_term_to_string`, `read_term_from_string`) |

The two `BodyOr` sites are phase invariants of the same family as
the `LambdaExpr` case below: the constructor survives in the type and
each pass asserts it was already lowered. A phase index on
`Desugared.BodyGoal` (or a post-lowering type without `BodyOr`) would
discharge both. The `Meta.hs` sites are the mildest — `invokeHostCall`
wraps the host function in `try @SomeException`
(`Interpreter.hs:872`), so they surface as an ordinary runtime error
rather than a process abort; they are nonetheless `error` rather than
`runtimeErrorS` for a difficulty that is really just arity.

### `R.LambdaExpr` survives lambda lifting — `src/YCHR/Run.hs:691`, `src/YCHR/Internal/Compile.hs:709`, `src/YCHR/Internal/Backend/SchemeDriver.hs:171`

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
emit/transfer path (`Var.hs:159-192`) and not blind-write
`Bound` — and the suggested constructor-hiding accessor module would
not encode it either: hiding the constructors centralizes the write
but still permits `writeVarState var (Bound v)` with `obs`
discarded.

The real defence is already in place and structural: `withUnboundVar`
(`Var.hs:120-130`) means every reader of the cell that needs its
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

Related, same "derive instead of store" shape: `VM.Program`
(`src/YCHR/Internal/VM/Types.hs:103,110`) stores `numTypes` next to
`typeNames` and `numRules` next to `ruleNames`, with the invariants
`numTypes == length typeNames` and `numRules == length ruleNames`
never checked. `Compile.hs:140-143` derives both pairs from the same
symbol table / rule list today. The counts are read by SExpr
serialization and the Scheme backend's `%make-session`, so removal is
a wider edit.

### VM IR `Int`/`ArgIndex` slots accept negatives — `src/YCHR/Internal/VM/Types.hs`

- `BMatchTerm ValExpr Name Int` (line 350) — arity slot.
- `GetArg ValExpr Int` (line 324) — index slot.
- `FieldArg IdExpr ArgIndex` (line 328) — `ArgIndex` is `newtype
  ArgIndex = ArgIndex Int` (line 438), so any signed value fits.

None of these use smart constructors. Switching to `Word` (or a
specialized non-negative newtype) is mechanical in the IR, **but it is
not the whole fix at the boundary**. `VM.SExpr`'s deserializer rebuilds
each slot with `fromInteger` with no range check
(`SExpr.hs:460,462,476,507` for `GetArg`, `FieldArg`, `BMatchTerm`, and
`Foreach` conditions). Under `Word`, `fromInteger (-1)` wraps to
`maxBound` silently, so the type change alone converts a raw negative
into a huge positive. The boundary needs an explicit
`parseNonNegative`/`Maybe` and an `Err` on failure; the type change is
the prerequisite that forces it to be written, not the check itself.
Two further wrinkles: `sargs !! idx` (`Store.hs:139,189`) takes `Int`,
so `suspArg`/`getConstraintArg` need a `Word -> Int` conversion, and
`matchTerm` compares against `length args` (`Var.hs:342-348`).

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

### Reactivation observer list is LIFO — `src/YCHR/Internal/Runtime/Var.hs:377`

```haskell
(\vid obs -> writeVarState var (Unbound vid (oid : obs)))
```

The reactivation order semantics is "most-recently registered first."
Documented only in code; a comment is enough for now, but worth a
named `Note [Observer registration order]` so it can't drift.


## 4. Undocumented invariants the implementation relies on

### `$call/N` supports N ∈ {1, …, 10}, enforced at resolution — `src/YCHR/Internal/Resolved.hs`

`maxCallArity = 10` in `YCHR.Internal.Resolved` is the single source of
truth for the supported dynamic-call arity. `Compile.genCallFunDispatches`
emits one `call_N` dispatcher per arity in `[1 .. maxCallArity]`, and
`Resolve.termToExpr` rejects a surface `'$call'` outside that range —
including zero, i.e. `'$call'(F)` and a bare `'$call'` — with
`UnsupportedCallArity` (YCHR-16022) while it recognizes the `'$call'`
shape.

Resolving rather than compiling is what makes the check total: programs,
queries and generated drivers all reach the compiler only through
`Resolve.termToExpr`, so none of them can produce an `ApplyExpr` whose
`call_N` procedure does not exist. The compiler's arity-generic
`callFunProcName` sites therefore do not need their own guard; they only
ever see an in-range arity.

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

Every `CallExpr` name (`tell_<c>/<n>`, `activate_<c>/<n>`,
`occurrence_<c>_<n>_<j>`, `func_<…>`, `call_N`,
`reactivate_dispatch`) must exist in the generated `procMap`. The
interpreter (`Interpreter.hs:397`) errors at runtime if any name is
missing. There is no whole-program closure check.

A post-compilation pass (or a typed `ProcRef` issued only by the
generator that introduces the procedure) would catch missing names
before runtime. Such a pass must run against the *unioned* procedure
map: `Run.hs` merges query-time procedures (lifted query lambdas and
regenerated `call_N` dispatches) into the map via
`Session.withCHRExtra`, so a check over the compiled program's map
alone would reject valid query-time calls.

### `reactivate_dispatch` covers every constraint type

Every `Unify`/body emits `DrainReactivationQueue → CallExpr
reactivate_dispatch`. The dispatch arms must list every constraint
type. If one is missed, reactivation of that type is a silent no-op
rather than an error. A typed dispatch table (parameterised by the
`ConstraintType` set) would close it.

### `tell_<c>/N` must exist for every constraint a query can ask for

`Session.tellConstraint` (`src/YCHR/Internal/Runtime/Session.hs:206-212`)
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

### Session construction — `src/YCHR/Internal/Runtime/Session.hs:121-135`

This entry described a layered effect stack (`runCHR` building
Unify → CHRStore → PropHistory → ReactQueue → Writer → CallStack →
CHR) that no longer exists: `Chr` is a `ReaderT SessionEnv IO`, and
`initSessionEnv` allocates every piece of session state into one
record. The ordering invariant went away with the stack.

What is left is weaker and lives in `withCHRExtra`: the procedure map
is `extraProcMap \`Map.union\` si.procIndex`, i.e. query-time
procedures deliberately *shadow* compiled ones on a name collision.
`Map.union` is left-biased, so swapping the operands silently
reverses that. Nothing but the argument order says which side wins.

### Scheme runtime ABI

`src/YCHR/Internal/Backend/Scheme.hs` bakes in many assumptions the Scheme
runtime must satisfy: the `(ychr runtime)` library is imported, every
procedure takes `%s` as its first parameter, return is via `call/cc`
with `%return`, the session thunk exported by each generated library
calls `(%make-session N)` directly, `drain-queue!` takes
`(session, alive-checking-lambda)`, `Foreach` expects
`(snapshot, count)` from the runtime. These contracts live only in
code, on both sides. A small ABI-doc section in
`SCHEME_BACKEND_GAPS.md` (or here) would at minimum make the surface
explicit; encoding it in types is harder because it crosses a
host-language boundary.


## Suggested next targets

If you want a roughly-ordered list of the most actionable wins:

1. **`ArgIndex` / `BMatchTerm` arity / `GetArg` index to a
   non-negative representation** (§2). Still worth doing, but not the
   mechanical swap an earlier revision called it: the `VM.SExpr`
   boundary rebuilds each slot with `fromInteger`
   (`SExpr.hs:460,462,476,507`), which wraps rather than rejects once
   the slot is `Word`, so a checked parser is required; `sargs !! idx`
   and `matchTerm`'s `length` comparison need `Int` conversions. Budget
   ~30 sites. Doing it closes the remaining `Store.hs` bounds entry in
   §1 (`getConstraintArg`; `suspArg` is already checked) in the sense
   that the compiler can no longer produce a negative index, and makes
   the boundary check meaningful.
2. **Procedure-name closure check** (§5). A post-compile pass that
   verifies every `CallExpr` resolves in the procedure map. Catches a
   whole class of compiler bugs at compile time. Must run against the
   *unioned* map — `Run.hs` adds query-time procedures that the
   compiled program's map does not contain.
3. **Phase-indexed `Expr`** (§1, `R.LambdaExpr`; and the two `BodyOr`
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
