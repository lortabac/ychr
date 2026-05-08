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
  `src/YCHR/Desugar.hs` that previously guarded the invariant. (Some
  rare paths still use `Types.qualifiedToName` to feed legacy helpers
  that operate on `Name`; those helpers can be migrated incrementally.)

- **Head Normal Form: post-HNF head args are variables or wildcards.**
  Encoded by introducing `Types.HeadArg = HeadVar Text | HeadWildcard`
  and `Types.HeadConstraint`, narrowing `Desugared.Head`'s `kept`/
  `removed`, `Desugared.Equation.params`,
  `Compile.Types.Occurrence.activeArgs`, and
  `Compile.Types.Partner.constraint` to the new types.
  `Desugar.normalizeArg` is the producer; the boundary helpers
  `headArgToTerm` and `headConstraintToConstraint` (in
  `YCHR.Types`) are used at the few sites in `TypeCheck.hs` that walk
  desugared heads through generic `Term` machinery. The list-
  comprehension drops in `Compile.buildVarMap` /
  `buildEquationVarMap` are now exhaustive matches on
  `HeadVar`/`HeadWildcard` instead of silent wide-`Term` filters.


## 1. `error` / `runtimeErrorS` for "can't happen" cases

Each of these crashes if the documented runtime invariant is violated.
A stronger type or a checked smart constructor would turn the runtime
panic into a compile-time error.

### Logical-variable deref invariant — `src/YCHR/Runtime/Var.hs:143,152,157,231,238`

Five sites all spell the same invariant:

```haskell
Bound {} -> error "unify': unexpected Bound after deref"
```

After `deref` returns a `VVar`, the variable must be `Unbound`. Today
the `VarState` type permits `Bound` regardless. A `newtype DerefedVar`
or a separate `UnboundVar` type returned from `deref` would let the
caller pattern-match exhaustively.

### `getArg` operand and bounds — `src/YCHR/Runtime/Var.hs:315-316`

```haskell
| otherwise -> error $ "getArg: index " ++ show idx ++ " out of bounds"
_ -> error "getArg: not a compound term"
```

`getArg` is partial on shape (must be `VTerm`) and on index. Callers
guarantee both, but neither is enforced. A typed term-projection API
keyed on a verified `(VTerm functor arity)` handle would close it.

### `lookupSusp` — `src/YCHR/Runtime/Store.hs:114`

```haskell
Nothing -> error $ "lookupSusp: unknown SuspensionId " ++ show sid
```

Every `SuspensionId` in circulation must have been allocated by
`createConstraint`. The header comment calls a miss "a runtime
invariant violation, not a user-facing failure" — exactly the case for
a typed handle (e.g. an opaque newtype that can only be created by the
allocation API).

### `getConstraintArg` bounds — `src/YCHR/Runtime/Store.hs:167`

```haskell
else error $ "getConstraintArg: index " ++ show idx ++ " out of bounds"
```

Same shape as `getArg`. The compiler is responsible for emitting only
in-range `ArgIndex` values; a smart-constructor for `ArgIndex` keyed
on the constraint type's arity (or a `Vector` of fixed length in the
suspension) would push the check up.

### Compiler-invariant guard on `RuntimeVal` — `src/YCHR/Runtime/Registry.hs:225`

```haskell
toValue (RConstraint _) = error "toValue: cannot convert constraint ID to Value"
```

The header comment marks this as the canonical compiler-invariant
guard: an `RConstraint` must never reach a `Value` position. See
§2 below — splitting the runtime into "values that can flow into
unification" and "constraint identifiers" would remove this and the
~12 sibling sites in the interpreter at once.

### Interpreter shape checks — `src/YCHR/Runtime/Interpreter.hs`

Twelve sites all phrase the same invariant: a particular VM instruction
operand must have a particular runtime shape.

| Line | Instruction              | Required operand              |
|------|--------------------------|-------------------------------|
| 153  | `CallExpr` dispatch      | name resolves in `procMap`    |
| 189  | `If`                     | `RVal (VBool _)`              |
| 206  | `Store`                  | `RConstraint _`               |
| 211  | `Kill`                   | `RConstraint _`               |
| 237  | `AddHistory` arg         | `RConstraint _`               |
| 301  | `Var`                    | name in scope                 |
| 322  | `HostCall`               | name in registry              |
| 330  | `Not`                    | boolean                       |
| 336  | `And` (1st arg)          | boolean                       |
| 342  | `Or` (1st arg)           | boolean                       |
| 361  | `Alive`                  | `RConstraint _`               |
| 367  | `IdEqual`                | both `RConstraint _`          |
| 372  | `IsConstraintType`       | `RConstraint _`               |
| 405  | `FieldGet`               | `RConstraint _`               |

All of these are compiler invariants — the compiler emits the right
shape by construction, but the type of `Expr` doesn't say so. A typed
VM IR (e.g. phantom-typed `Expr 'BoolKind` vs. `Expr 'ValueKind` vs.
`Expr 'ConstraintIdKind`) would let the interpreter's `case` arms be
total.

### `ConstraintType (-1)` placeholder — `src/YCHR/Compile/Occurrences.hs:171`

```haskell
pure (ConstraintType (-1))
```

When the symbol-table lookup misses, an out-of-band `(-1)` is returned
and a diagnostic is emitted. The runtime's `getStoreSnapshot`
(`src/YCHR/Runtime/Store.hs`) defensively returns `Seq.empty` for
out-of-range indices — so the placeholder *almost* survives, but only
because the store is defensive. Either:

- Encode "lookup failed, error already reported" as `Maybe
  ConstraintType` and change downstream code to skip those occurrences
  cleanly, or
- Make `ConstraintType` a wrapped `Word` so `(-1)` cannot be
  constructed.


## 2. Data types that admit invalid states

### `RuntimeVal` is too wide for unification positions — `src/YCHR/Runtime/Types.hs`

```haskell
data RuntimeVal = RVal Value | RConstraint SuspensionId
```

Roughly half the interpreter's `runtimeErrorS` sites (Store, Kill,
AddHistory, Alive, IdEqual, IsConstraintType, FieldGet) and the
`toValue` panic in `Registry.hs` are all the same invariant: the
operand must be `RConstraint` (or, dually, must be `RVal`). Splitting
`RuntimeVal` into two distinct types passed through differently-typed
VM operands would make every one of those `case` arms total.

### `VarState` admits orphan observers — `src/YCHR/Runtime/Types.hs:28-33`

```haskell
data VarState = Unbound !VarId ![SuspensionId] | Bound !Value
```

Observer lists are meaningful only on `Unbound`; once a variable is
bound, the observers are emitted and the list is moot. Today nothing
prevents a hypothetical caller from constructing a `Bound` value with
a stale observer list. A small accessor module that hides the
constructors and only exposes "bind (drains observers)" / "register
observer (only on Unbound)" would lock this down.

### Compiler IR carries unchecked arity fields — `src/YCHR/Compile/Types.hs`

- `Occurrence { conArity :: Int, activeArgs :: [Term] }` — nothing
  enforces `conArity == length activeArgs`. Generated `FieldArg`
  indices are derived from `conArity`; if it disagreed with
  `activeArgs`, the runtime would silently access wrong fields.
- `Partner { constraint :: QualifiedConstraint }` — `length
  constraint.args` is assumed to match the symbol table's recorded
  arity; not cross-checked.
- `IndexCondition { argIndex :: ArgIndex, ... }` — `argIndex` is not
  bounds-checked against the partner's arity at construction. The
  compiler trusts itself.

A common fix: make arity a `newtype` and have a smart constructor for
`Occurrence`/`Partner`/`IndexCondition` that reconciles or rejects
mismatches.

### VM IR `Int`/`ArgIndex` slots accept negatives — `src/YCHR/VM/Types.hs`

- `MatchTerm Expr Name Int` (line 235) — arity slot.
- `GetArg Expr Int` (line 237) — index slot.
- `FieldArg ArgIndex` — `ArgIndex` is `newtype ArgIndex = ArgIndex Int`,
  so any signed value fits.

None of these use smart constructors. Switching to `Word` (or a
specialized non-negative newtype) is mechanical.


## 3. Documented invariants worth promoting into types

### Occurrence numbering is 1-based — `src/YCHR/Compile/Occurrences.hs:61`

```haskell
assignNumbers = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..]
```

Paper §ωr requires 1-based numbering. The `OccurrenceNumber` newtype
is unconstrained; a smart constructor `mkOccurrenceNumber :: Int ->
Maybe OccurrenceNumber` (or starting from `1` only) would enforce it.

### Reverse-ordered accumulator lists — `src/YCHR/Desugar.hs`

- `HnfState.guards` (~line 188): "accumulated in reverse".
- `LiftState.liftedFunctions` (~line 438): "in reverse discovery
  order".

Both are reversed exactly once, by discipline. A `newtype Reverse a =
Reverse [a]` (or `Data.Sequence`) makes the order visible.

### `tc_unify` argument order — `src/YCHR/TypeCheck.hs:11-26`

The module header documents that source-variable types must be on the
left and declared types on the right when calling `tc_unify` from CHR.
Today, this is enforced by routing every cross-comparison through
named helpers (`check_constraint_use`, `check_function_use`,
`check_constructor_use`). A `newtype SourceTypeVar` / `newtype
DeclaredTypeVar` wrapper around `Value` would make the `tellConstraint`
call site total.

### Reactivation observer list is LIFO — `src/YCHR/Runtime/Var.hs:327`

```haskell
Unbound vid obs -> writeVarState var (Unbound vid (oid : obs))
```

The reactivation order semantics is "most-recently registered first."
Documented only in code; a comment is enough for now, but worth a
named `Note [Observer registration order]` so it can't drift.


## 4. Undocumented invariants the implementation relies on

### `$call/N` only supports N ∈ {1, 2} — `src/YCHR/Compile.hs` (~line 861)

The compiler hardcodes `genCallFunDispatch` for `[1, 2]`. A user
program with `$call/3` or higher produces a `CallExpr` whose name
never resolves at runtime. There is no compile-time diagnostic.

Either widen the supported set (cheap) or add a
`UnsupportedCallArity` `CompileError` and fail early.

### `partArity` derived from desugared head matches runtime constraint shape — `src/YCHR/Compile.hs:325`

```haskell
partArity = length partner.constraint.args
```

`partArity` is used to generate `FieldArg` indices into the partner
suspension. The compiler assumes the symbol-table arity for that
constraint type matches the desugared-head arity. A symbol-table
mismatch (which `lookupCType` *can* return as `(-1)`) would cause the
runtime to access out-of-bounds fields. See §1's `(-1)` placeholder
entry — the two issues meet here.

### `classifyEqual` returns an unbounded `ArgIndex` — `src/YCHR/Compile.hs:589-600`

`asPartnerArg` produces an `(ArgIndex, …)` pair that is baked into an
`IndexCondition` without any bounds check against the partner
constraint's arity. Same fix shape as §2's `IndexCondition` entry —
construct via a smart constructor that takes the partner's arity.

### `History` keys assume canonical `SuspensionId` ordering — `src/YCHR/Runtime/History.hs:54-62`

History is keyed by `(RuleId, [SuspensionId])`. Equality is on the
list shape; the caller must build the list in a canonical order at
every call site. Today `Compile.hs` builds it consistently, but no
type insists. A `Set SuspensionId` (where order doesn't matter) or a
sorted `Vector` would close it.

### Symbol-table lookup for unknown constructor falls through to `any` — `src/YCHR/TypeCheck.hs:587-591`

```haskell
let withinArity =
      case Map.lookup conName env.conMap of
        Just (_, dc) -> idx < length dc.conArgs
        Nothing -> True -- unknown constructor → unknown_guard_getarg handles it
```

The check phase silently skips out-of-range indices on unknown
constructors, on the assumption that a separate pre-pass
(`validateConstructorArities`) reported the error. That coupling is
not visible at the type. A dedicated `KnownCtorRef` /
`UnknownCtorRef` split, or invariants on `conMap` membership, would
make it explicit.


## 5. Cross-cutting compiler ↔ runtime contracts

These span the compiler/runtime boundary. The compiler emits one
shape, the runtime consumes another; nothing on either side checks
that they agree.

### Closed procedure-name set

Every `CallExpr` name (`tell_<c>/<n>`, `activate_<c>/<n>`,
`occurrence_<c>_<n>_<j>`, `func_<…>`, `call_N`,
`reactivate_dispatch`) must exist in the generated `procMap`. The
interpreter (`Interpreter.hs:153`) errors at runtime if any name is
missing. There is no whole-program closure check.

A post-compilation pass (or a typed `ProcRef` issued only by the
generator that introduces the procedure) would catch missing names
before runtime.

### `reactivate_dispatch` covers every constraint type

Every `Unify`/body emits `DrainReactivationQueue → CallExpr
reactivate_dispatch`. The dispatch arms must list every constraint
type. If one is missed, reactivation of that type is a silent no-op
rather than an error. A typed dispatch table (parameterised by the
`ConstraintType` set) would close it.

### `tell_<c>/N` must exist for every constraint a query can ask for

`Session.tellConstraint` (`src/YCHR/Runtime/Session.hs:183-191`)
resolves a name and arity through the export map and calls
`tellProcName resolved arity`. The compiler must have generated
exactly that procedure. Failure surfaces at query time, not compile
time.

### `Store` linearly follows `CreateConstraint`

Runtime observer registration in `Store.hs:136-143` is correct only
for a freshly-created suspension. The VM's IR is structured so
`Store` always follows `CreateConstraint` for the same id, but that
linear order is not encoded — a sufficiently exotic compiler output
could break the runtime silently.

### Effect-stack ordering — `src/YCHR/Runtime/Session.hs:126-134`

`runCHR` builds a fixed stack: Unify → CHRStore → PropHistory →
ReactQueue → Writer → CallStack → CHR. Any reorder either fails to
type-check or changes semantics; no `Note` documents the
constraint. Worth either a `Note [Effect stack ordering]` or a typed
`runCHR :: ChrInputs -> Eff ChrLayer a -> IO a` wrapper that hides
the layer construction.

### Scheme runtime ABI

`src/YCHR/Backend/Scheme.hs` bakes in many assumptions the Scheme
runtime must satisfy: the `(ychr runtime)` library is imported, every
procedure takes `%s` as its first parameter, return is via `call/cc`
with `%return`, `%init!` takes the type count, `drain-queue!` takes
`(session, alive-checking-lambda)`, `Foreach` expects
`(snapshot, count)` from the runtime. These contracts live only in
code, on both sides. A small ABI-doc section in
`SCHEME_BACKEND_GAPS.md` (or here) would at minimum make the surface
explicit; encoding it in types is harder because it crosses a
host-language boundary.


## Suggested next targets

If you want a roughly-ordered list of the most actionable wins:

1. **`RuntimeVal` split** (§2). Single change, removes ~12 interpreter
   `runtimeErrorS` sites and the `toValue` panic.
2. **`ArgIndex` / `MatchTerm` arity to `Word`** (§2). Cheap, removes
   a class of bounds-related bugs.
3. **`ConstraintType` as `Word`** plus `Maybe ConstraintType` for
   lookup (§1). Removes the `(-1)` sentinel.
4. **Procedure-name closure check** (§5). A post-compile pass that
   verifies every `CallExpr` resolves in the program's procedure map.
   Catches a whole class of compiler bugs at compile time.
