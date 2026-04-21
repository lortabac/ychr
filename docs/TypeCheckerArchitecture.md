# Type Checker Architecture

This document specifies the architecture for the YCHR type checker.
The type checker implements the type system described in
`TypeSystem.md`.

The type checker is a CHR program (`typechecker.chr`) compiled via
Template Haskell and driven by a Haskell module that walks the
desugared AST and feeds constraints into a CHR session.


## Overview

```
Desugared.Program
       │
       ▼
  Haskell Driver (YCHR.TypeCheck)
       │
       │  1. tells environment: constraint_sig, function_sig, con_sig
       │  2. per rule/equation: tells check_* constraints
       │  3. tells collect(E) to retrieve errors
       ▼
  CHR Session (typechecker.chr)
       ��
       │  matches usages against stored declarations
       │  instantiates fresh type copies via copy_term
       │  runs tc_unify (any-aware consistency)
       │  accumulates errors in ordinary list
       ▼
  Haskell Driver reads E
       │
       ▼
  [] → success  |  [err, ...] → TypeCheckErrors
```


## Division of Labor

| Responsibility | Haskell | CHR |
|---|---|---|
| Walk AST (rules, equations, guards, bodies) | Yes | No |
| Create fresh type variables for source variables | Yes | No |
| Compute type of literal expressions | Yes | No |
| Type definition validation (bound vars, defined types) | Yes | No |
| Encode `TypeExpr` to runtime type terms | Yes | No |
| Store declarations, match usages by name | No | Yes |
| Instantiate declarations with fresh types (`copy_term`) | No | Yes |
| `tc_unify` with `any`-awareness | No | Yes |
| Error accumulation and collection | No | Yes |


## Type Representation

Types are represented as runtime `Value` terms. Type parameters in
declarations are logical variables; `copy_term` creates fresh copies
at each use site.

| Type | Value encoding |
|---|---|
| `int` | `VAtom "int"` |
| `string` | `VAtom "string"` |
| `any` | `VAtom "any"` |
| type parameter (in decl) | `VVar v` (fresh logical variable) |
| `list(A)` | `VTerm "tcon" [VAtom "list", [A]]` |
| `option(A)` | `VTerm "tcon" [VAtom "option", [A]]` |
| `fun(int, int) -> bool` | `VTerm "fun" [[int, int], bool_type]` |
| `fun(A) -> A` | `VTerm "fun" [[VVar a], VVar a]` |

In CHR source syntax:

| Type | CHR term |
|---|---|
| `int` | `int` |
| `string` | `string` |
| `any` | `any` |
| `list(A)` | `tcon(list, [A])` |
| `fun(int, int) -> bool` | `fun([int, int], tcon(bool, []))` |

Type constructor names are fully qualified atoms (e.g.,
`prelude:bool`, `prelude:list`). Base types `int`, `string`, `any`
are bare atoms.

### Encoding in Haskell

The Haskell driver converts `TypeExpr` values to `Value` terms:

```
encodeTypeExpr(tvars, TypeVar v)           = tvars[v]
encodeTypeExpr(tvars, TypeCon "int" [])    = VAtom "int"
encodeTypeExpr(tvars, TypeCon "string" []) = VAtom "string"
encodeTypeExpr(tvars, TypeCon "any" [])    = VAtom "any"
encodeTypeExpr(tvars, TypeCon name args)   =
    VTerm "tcon" [VAtom (flattenName name),
                  valueList (map (encodeTypeExpr tvars) args)]
```

For function types:

```
encodeFunType(argTypes, retType) =
    VTerm "fun" [valueList argTypes, retType]
```

The `tvars` map is created per declaration: for each type variable
name in the declaration, a fresh logical variable is created. These
variables are shared across the declaration's argument types, so
`member(A, list(A))` has the same `VVar` for both `A`s.


## Contract: CHR Constraints

### Environment constraints

Told once per program element, before any checking begins.

#### `constraint_sig/2`

```
constraint_sig(Name, ArgTypes)
```

- **Name**: qualified atom (e.g., `order:leq`)
- **ArgTypes**: list of type terms, with logical variables for type
  parameters

Missing type annotations produce `any` for all arguments.

Examples:

- `:- chr_constraint leq(int, int)` →
  `constraint_sig(order:leq, [int, int])`
- `:- chr_constraint member(A, list(A))` →
  `constraint_sig(m:member, [α, tcon(m:list, [α])])` where `α` is
  a fresh logical variable
- `:- chr_constraint foo/2` →
  `constraint_sig(m:foo, [any, any])`

#### `function_sig/2`

```
function_sig(Name, sig(ArgTypes, RetType))
```

- **Name**: qualified atom
- **sig(ArgTypes, RetType)**: compound term wrapping argument types
  and return type (so `copy_term` preserves sharing between them)

Example: `:- function sign(int) -> result` ��
`function_sig(m:sign, sig([int], tcon(m:result, [])))`.

#### `con_sig/2`

```
con_sig(ConName, sig(ParentType, FieldTypes))
```

- **ConName**: qualified atom
- **sig(ParentType, FieldTypes)**: compound wrapping the parent
  algebraic type and the field types (sharing type variables)

Example: for `option(A) ---> none ; some(A)`:

```
con_sig(m:none, sig(tcon(m:option, [α₁]), []))
con_sig(m:some, sig(tcon(m:option, [α₂]), [α₂]))
```

Each constructor's `con_sig` has its own fresh variables. The
sharing within `sig(...)` ensures `copy_term` produces consistent
instantiations.

### Checking constraints

Told per usage site within a rule or function equation scope.

#### `check_constraint_use/3`

```
check_constraint_use(Name, ArgTypeVars, Ctx)
```

Told for each constraint occurrence in a rule head or body.
`ArgTypeVars` is a list of type variables (one per argument),
computed by the Haskell driver via `typeOfTerm`.

#### `check_function_use/4`

```
check_function_use(Name, ArgTypeVars, RetTypeVar, Ctx)
```

Told for each function call in a guard, `is` RHS, or body.

#### `check_constructor_use/4`

```
check_constructor_use(ConName, ArgTypeVars, ResultTypeVar, Ctx)
```

Told for each known constructor in an expression. Unknown
constructors are typed as `any` by the driver; no constraint is
told.

#### `check_unify/3`

```
check_unify(TypeVar1, TypeVar2, Ctx)
```

Told for each body unification (`X = Y`). Delegates to `tc_unify`.

#### `check_guard_bool/2`

```
check_guard_bool(TypeVar, Ctx)
```

Told for each guard expression. Asserts type is consistent with
`bool`.

#### `check_guard_match/3`

```
check_guard_match(TermTypeVar, ConName, Ctx)
```

Told for `GuardMatch` (HNF pattern match). Constrains the term's
type to be consistent with the algebraic type containing the named
constructor.

#### `check_guard_getarg/5`

```
check_guard_getarg(ResultTypeVar, TermTypeVar, ConName, FieldIndex, Ctx)
```

Told for `GuardGetArg` (HNF argument extraction). The constructor
name is needed to look up the correct `con_sig`. The Haskell driver
pairs it with the constructor from the preceding `GuardMatch`.

### Lifecycle constraints

#### `errors/1`

```
errors(ErrorList)
```

Told at the start with an empty list: `errors([])`.

#### `collect/1`

```
collect(E)
```

Told at the end. `E` is a fresh logical variable. A CHR rule binds
`E` to the accumulated error list.


## CHR Type-Checker Rules

### Declaration matching

```prolog
%% Constraint usage: copy_term the declaration, check args pairwise
constraint_sig(Name, DeclTypes) \
    check_constraint_use(Name, ArgTypes, Ctx) <=>
    copy_term(DeclTypes, FreshTypes),
    check_arg_list(FreshTypes, ArgTypes, Ctx).

%% Unknown constraint
check_constraint_use(Name, _, Ctx) <=>
    report_error(Ctx, unknown_constraint, Name).

%% Function usage: copy_term preserves arg/ret sharing
function_sig(Name, Sig) \
    check_function_use(Name, ArgTypes, RetTypeVar, Ctx) <=>
    copy_term(Sig, sig(FreshArgTypes, FreshRetType)),
    check_arg_list(FreshArgTypes, ArgTypes, Ctx),
    tc_unify(RetTypeVar, FreshRetType, Ctx).

%% Unknown function
check_function_use(Name, _, _, Ctx) <=>
    report_error(Ctx, unknown_function, Name).

%% Constructor usage: copy_term preserves parent/field sharing
con_sig(ConName, Sig) \
    check_constructor_use(ConName, ArgTypes, ResultTypeVar, Ctx) <=>
    copy_term(Sig, sig(FreshParent, FreshFields)),
    check_arg_list(FreshFields, ArgTypes, Ctx),
    tc_unify(ResultTypeVar, FreshParent, Ctx).

%% Unknown constructor → any (not an error)
check_constructor_use(_, _, ResultTypeVar, _) <=>
    ResultTypeVar = any.
```

### Argument list checking

```prolog
check_arg_list([D|Ds], [A|As], Ctx) <=>
    tc_unify(A, D, Ctx),
    check_arg_list(Ds, As, Ctx).
check_arg_list([], [], _) <=> true.
```

### Delegation rules

```prolog
check_unify(T1, T2, Ctx) <=> tc_unify(T1, T2, Ctx).

check_guard_bool(T, Ctx) <=>
    tc_unify(T, tcon(prelude:bool, []), Ctx).

con_sig(ConName, Sig) \
    check_guard_match(TermType, ConName, Ctx) <=>
    copy_term(Sig, sig(FreshParent, _)),
    tc_unify(TermType, FreshParent, Ctx).

%% Unknown constructor in guard match → no type info (any)
check_guard_match(_, _, _) <=> true.

con_sig(ConName, Sig) \
    check_guard_getarg(ResultType, TermType, ConName, FieldIndex, Ctx) <=>
    copy_term(Sig, sig(FreshParent, FreshFields)),
    tc_unify(TermType, FreshParent, Ctx),
    FieldType is nth(FieldIndex, FreshFields),
    tc_unify(ResultType, FieldType, Ctx).

%% Unknown constructor in guard getarg → result is any
check_guard_getarg(ResultType, _, _, _, _) <=> ResultType = any.
```

### tc_unify (type propagation and consistency)

The core operation. Performs two roles:

1. **Propagation**: when a variable with unknown type meets a
   concrete type, binds the variable to that type.
2. **Consistency**: when two concrete types meet, verifies they are
   compatible.

The `any` type is special: it binds unknown (unbound) variables that
meet it, making them `any`. However, it does not overwrite variables
that already have a concrete type, and it does not bind declared
type parameters. This requires careful rule ordering — see the
rationale section below.

```prolog
%% --- any handling (must come first) ---

%% (1) Nonvar any on left → succeed, don't touch right side
tc_unify(T1, _, _) <=> nonvar(T1), T1 == any | true.

%% (2) Both nonvar, any on right → succeed
tc_unify(T1, T2, _) <=> nonvar(T1), nonvar(T2), T2 == any | true.

%% (3) Var on left, any on right → bind var to any
tc_unify(T1, T2, _) <=> var(T1), nonvar(T2), T2 == any | T1 = any.

%% --- base types ---

tc_unify(int, int, _) <=> true.
tc_unify(string, string, _) <=> true.

%% --- type constructors: same name, check args ---

tc_unify(tcon(C, Args1), tcon(C, Args2), Ctx) <=>
    tc_unify_list(Args1, Args2, Ctx).

%% --- function types ---

tc_unify(fun(A1, R1), fun(A2, R2), Ctx) <=>
    tc_unify_list(A1, A2, Ctx),
    tc_unify(R1, R2, Ctx).

%% --- var rules ---

tc_unify(T1, T2, _) <=> var(T1), nonvar(T2) | T1 = T2.
tc_unify(T1, T2, _) <=> nonvar(T1), var(T2) | T2 = T1.
tc_unify(T1, T2, _) <=> var(T1), var(T2) | T1 = T2.

%% --- fallback: inconsistency ---

tc_unify(T1, T2, Ctx) <=> nonvar(T1), nonvar(T2) |
    report_error(Ctx, inconsistent, pair(T1, T2)).
```

### tc_unify_list

```prolog
tc_unify_list([], [], _) <=> true.
tc_unify_list([H1|T1], [H2|T2], Ctx) <=>
    tc_unify(H1, H2, Ctx),
    tc_unify_list(T1, T2, Ctx).
```

### Error accumulation

```prolog
report_error(Ctx, Code, Detail), errors(Es) <=>
    errors([error(Ctx, Code, Detail) | Es]).

collect(E), errors(Es) <=> E = Es.
```

### Rationale: tc_unify rule ordering

The `any` rules must come first and are carefully structured to
handle two distinct cases:

**Case A — source variable meets `any` from declaration:**
The driver tells `tc_unify(TX, any, ctx)` where `TX` is an unbound
var. Rule (1) fails (`nonvar(TX)` is false). Rule (2) fails
(`nonvar(TX)` is false). Rule (3) fires: `var(TX)` true, `any ==
any` true → `TX = any`. The source variable becomes `any`, which
is correct: the declaration says this position is untyped.

**Case B — pre-bound `any` meets type parameter from declaration:**
The driver tells `tc_unify(any, α', ctx)` where `α'` is a fresh
type parameter from `copy_term`. Rule (1) fires: `nonvar(any)` true,
`any == any` true → succeed. `α'` is NOT bound. This is correct:
the type parameter should remain open so that other argument
positions can still constrain it.

The asymmetry is intentional:

- `tc_unify(var, any, ...)` → bind to `any` (rule 3)
- `tc_unify(any, var, ...)` → succeed, don't bind (rule 1)

This works because the Haskell driver always tells constraints with
the source variable's type on the LEFT and the declared type on the
RIGHT: `tc_unify(sourceVarType, declaredType, ctx)`.

**Invariant**: the driver MUST maintain this argument order. Body
unifications (`X = Y`) use `tc_unify(TX, TY, ctx)` where both are
source variable types — these are symmetric (both are either bound
or unbound vars), so the asymmetry does not cause issues.


## Haskell Driver Algorithm

### Pipeline integration

Type checking runs after desugaring, before compilation:

```
parse → rename → resolve → desugar → lambda-lift → TYPE CHECK → compile
```

Controlled by a flag. When disabled, the phase is skipped entirely.

### Top-level algorithm

```
typeCheckProgram(prog):
  compiled = compileTH("typechecker.chr")  -- at TH time
  withCHR compiled $ do
    -- 1. Tell environment
    tell errors([])
    tellConstraintDecls(prog.constraintTypes)
    tellFunctionDecls(prog.functions)
    tellConstructorDecls(prog.typeDefinitions)

    -- 2. Validate type definitions (Haskell-side)
    typeDefErrors = validateTypeDefinitions(prog.typeDefinitions)

    -- 3. Check each rule
    for rule in prog.rules:
      checkRule(prog, rule)

    -- 4. Check each function equation
    for func in prog.functions:
      for eq in func.equations:
        checkEquation(prog, func, eq)

    -- 5. Collect errors
    errVar <- newVar
    tell collect(errVar)
    errList <- deref errVar
    return typeDefErrors ++ decodeErrors(errList)
```

### Per-rule checking

```
checkRule(prog, rule):
  -- Fresh type variable for each source variable in the rule
  allVarNames = collectVarsInRule(rule)
  varTypes = Map.fromList [(v, newVar()) | v <- allVarNames]

  -- Head constraints (kept and removed)
  for con in rule.head.kept ++ rule.head.removed:
    argTypeVars = [typeOfTerm(varTypes, prog, arg) | arg <- con.args]
    ctx = mkCtx(rule, con)
    tell check_constraint_use(con.name, argTypeVars, ctx)

  -- Guards
  for guard in rule.guard:
    case guard of
      GuardEqual t1 t2 ->
        tell check_unify(typeOfTerm(varTypes, prog, t1),
                         typeOfTerm(varTypes, prog, t2), ctx)
      GuardMatch term conName arity ->
        lastConName = conName  -- remember for subsequent GuardGetArg
        tell check_guard_match(
            typeOfTerm(varTypes, prog, term), conName, ctx)
      GuardGetArg varName term index ->
        -- uses lastConName from the preceding GuardMatch on this term
        tell check_guard_getarg(varTypes[varName],
            typeOfTerm(varTypes, prog, term),
            lastConName, index, ctx)
      GuardExpr term ->
        tell check_guard_bool(
            typeOfTerm(varTypes, prog, term), ctx)

  -- Body goals
  for goal in rule.body:
    case goal of
      BodyConstraint con ->
        argTypeVars = [typeOfTerm(varTypes, prog, a) | a <- con.args]
        tell check_constraint_use(con.name, argTypeVars, ctx)
      BodyUnify t1 t2 ->
        tell check_unify(typeOfTerm(varTypes, prog, t1),
                         typeOfTerm(varTypes, prog, t2), ctx)
      BodyIs var term ->
        tell tc_unify(varTypes[var],
                      typeOfTerm(varTypes, prog, term), ctx)
      BodyFunctionCall name args ->
        argTypeVars = [typeOfTerm(varTypes, prog, a) | a <- args]
        retTypeVar = newVar()
        tell check_function_use(name, argTypeVars, retTypeVar, ctx)
      BodyHostStmt _ args ->
        -- Process arguments for side effects (nested typed terms
        -- still get checked) but don't constrain them.
        mapM_ (typeOfTerm varTypes prog) args
      BodyTrue -> skip
```

### Per-equation checking

```
checkEquation(prog, func, eq):
  varTypes = Map.fromList [(v, newVar()) | v <- collectVarsInEq(eq)]
  freshTVars = freshTypeVarsForDecl(func)

  -- Parameter types from declaration
  for (param, declTypeExpr) in zip(eq.params, func.argTypes):
    paramType = typeOfTerm(varTypes, prog, param)
    declType = encodeTypeExpr(freshTVars, declTypeExpr)
    tell tc_unify(paramType, declType, ctx)

  -- Guards (same as rule guards)
  ...

  -- RHS must be consistent with declared return type
  rhsType = typeOfTerm(varTypes, prog, eq.rhs)
  retType = encodeTypeExpr(freshTVars, func.returnType)
  tell tc_unify(rhsType, retType, ctx)
```

### typeOfTerm

Recursively determines the type of a term expression.

```
typeOfTerm(varTypes, prog, term):
  case term of
    VarTerm v     -> varTypes[v]
    IntTerm _     -> VAtom "int"
    TextTerm _    -> VAtom "string"
    AtomTerm s    -> typeOfAtom(prog, s)
    CompoundTerm name args -> typeOfCompound(varTypes, prog, name, args)
    Wildcard      -> newVar()  -- unconstrained

typeOfAtom(prog, s):
  if s is a known nullary constructor:
    resultType = newVar()
    tell check_constructor_use(s, [], resultType, ctx)
    return resultType
  else:
    return VAtom "any"

typeOfCompound(varTypes, prog, name, args):
  if name is a known constructor:
    argTypes = [typeOfTerm(varTypes, prog, a) | a <- args]
    resultType = newVar()
    tell check_constructor_use(name, argTypes, resultType, ctx)
    return resultType
  if name is a known function:
    argTypes = [typeOfTerm(varTypes, prog, a) | a <- args]
    resultType = newVar()
    tell check_function_use(name, argTypes, resultType, ctx)
    return resultType
  -- Unknown constructor or host call: process arguments for side effects
  -- (nested constructors / function calls still get type-checked) but
  -- don't constrain them — each argument position is effectively `any`.
  mapM_ (typeOfTerm varTypes prog) args
  return VAtom "any"
```


## Error Format

### Context term

```
ctx(Phase, Label)
```

- **Phase**: `rule(RuleName)` or `equation(FuncName, Index)` or
  `typedef(TypeName)`
- **Label**: human-readable position description (atom)

Source locations are not in the CHR-level context. The Haskell driver
maps contexts back to source locations when formatting errors.

### Error term

```
error(Ctx, Code, Detail)
```

### Error codes

| Code | Meaning | Detail |
|---|---|---|
| `inconsistent` | Two types are inconsistent | `pair(T1, T2)` |
| `unknown_constraint` | Constraint not declared | Name |
| `unknown_function` | Function not declared | Name |

Haskell-side validation errors (not CHR):

| Code | Meaning |
|---|---|
| `unbound_type_var` | Type var in constructor not bound by header |
| `undefined_type` | Type referenced in constructor field not defined |


## Required CHR Features

### Available

| Feature | Used for |
|---|---|
| Pattern matching in heads | `tcon(C, Args)`, `fun(A, R)`, etc. |
| Shared variables in heads | Same `C` in `tcon(C, A1), tcon(C, A2)` |
| Simpagation (`\`) | Keep declarations, consume checks |
| Unification (`=`) in bodies | Binding type vars, error collection |
| List syntax `[H\|T]`, `[]` | Arg lists, error lists |
| Guards: `var/1`, `nonvar/1` | Testing type variable state |
| Guards: `==` | Testing `T == any` without binding |
| User-defined functions | `nth` |
| `is` for function results | `FieldType is nth(...)` |
| Rule ordering | `any` rules before `var` rules |
| Arithmetic | `nth` indexing |

### New features required

#### `copy_term/2`

New built-in constraint. `copy_term(Original, Copy)` deep-copies a
term, replacing each unbound logical variable with a fresh one while
preserving sharing (same original variable → same fresh copy).
`Copy` is unified with the result.

Implemented as a constraint (not a function) because functions
evaluate their arguments, which would force the input term before
copying -- defeating the purpose.

```prolog
:- chr_constraint copy_term/2.
```

The implementation is a host-level built-in (like `store` or
`kill`), not a user-level CHR rule. The runtime handles it directly.

Haskell implementation sketch:

```haskell
copyTerm :: (Unify :> es, IOE :> es) => Value -> Eff es Value
copyTerm val = evalState Map.empty (go val)
  where
    go v = do
      v' <- deref v
      case v' of
        VVar _ -> do
          vid <- getVarId v'
          cache <- get
          case Map.lookup vid cache of
            Just fresh -> pure fresh
            Nothing -> do
              fresh <- newVar
              modify (Map.insert vid fresh)
              pure fresh
        VTerm f args -> VTerm f <$> traverse go args
        other -> pure other
```

#### `nth/2`

List indexing. To be added to the `lists` library.

### Not required

| Feature | Why not needed |
|---|---|
| `=..` (univ) | Explicit constructors: `tcon`, `fun` |
| `findall` / `bagof` | Ordinary list accumulation |
| `assert` / `retract` | CHR constraints as store |
| Difference lists | Not supported; using ordinary lists |
| `\==` | Rule ordering handles it |


## Bootstrapping

The type-checker CHR program is compiled at TH time, following the
pattern of `src/YCHR/StdLib/TH.hs`. The compilation uses the
pipeline with type checking disabled to avoid bootstrapping
recursion.


## File Organization

### New files

| File | Purpose |
|---|---|
| `typechecker/typechecker.chr` | The CHR type-checker program |
| `src/YCHR/TypeCheck.hs` | Haskell driver |
| `src/YCHR/TypeCheck/TH.hs` | TH splice for typechecker.chr |
| `test/YCHR/TypeCheckTest.hs` | Tests |

### Modified files

| File | Change |
|---|---|
| `src/YCHR/Run.hs` | `TypeCheckErrors` in `Error`; pipeline wiring |
| `src/YCHR/Display.hs` | Error codes and display |
| `src/YCHR/Runtime/Registry.hs` | `copy_term` built-in constraint |
| `ychr.cabal` | New modules, data file |


## Worked Examples

### Well-typed: leq transitivity

```prolog
:- chr_constraint leq(int, int).
transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

Environment: `constraint_sig(leq, [int, int])`.

1. Fresh vars: TX, TY, TZ.
2. Head `leq(X, Y)`: `copy_term([int, int], FT)` → FT = `[int, int]`.
   `tc_unify(TX, int, ctx)` → TX = int.
   `tc_unify(TY, int, ctx)` → TY = int.
3. Head `leq(Y, Z)`: `copy_term([int, int], FT)` → FT = `[int, int]`.
   `tc_unify(TY, int, ctx)` → TY is int, match → succeed.
   `tc_unify(TZ, int, ctx)` → TZ = int.
4. Body `leq(X, Z)`: `copy_term([int, int], FT)` → FT = `[int, int]`.
   `tc_unify(TX, int, ctx)` → succeed.
   `tc_unify(TZ, int, ctx)` → succeed.
5. **Result: no errors. ✓**

### Ill-typed: conflicting types

```prolog
:- chr_constraint foo(int), bar(string).
bad @ foo(X), bar(X) <=> true.
```

1. Fresh vars: TX.
2. Head `foo(X)`: `tc_unify(TX, int, ctx)` → TX = int.
3. Head `bar(X)`: `tc_unify(TX, string, ctx)` → TX is int,
   string ≠ int, both nonvar → `report_error(ctx, inconsistent,
   pair(int, string))`.
4. **Result: `[error(ctx, inconsistent, pair(int, string))]`. ✓**

### Gradual: any absorption

```prolog
:- chr_constraint foo(any), bar(int), baz(bool).
mix @ foo(X), bar(Y), baz(Z) <=> X = Y, X = Z.
```

1. Fresh vars: TX, TY, TZ.
2. Head `foo(X)`: `tc_unify(TX, any, ctx)`.
   Rule (1): `nonvar(TX)` false (TX is var) → skip.
   Rule (2): `nonvar(TX)` false → skip.
   Rule (3): `var(TX)` true, `any == any` true → TX = any.
3. Head `bar(Y)`: `tc_unify(TY, int, ctx)` → TY = int.
4. Head `baz(Z)`: `tc_unify(TZ, tcon(bool,[]), ctx)` → TZ = tcon(bool,[]).
5. Body `X = Y`: `tc_unify(TX, TY, ctx)` = `tc_unify(any, int, ctx)`.
   Rule (1): `nonvar(any)` true, `any == any` true → succeed.
6. Body `X = Z`: `tc_unify(TX, TZ, ctx)` = `tc_unify(any, tcon(bool,[]), ctx)`.
   Rule (1): succeed.
7. **Result: no errors. ✓**

### Polymorphic: type parameter not bound to any

```prolog
:- chr_constraint qux(any), foo(A, A), bar(int).
rule @ qux(X), foo(X, Y), bar(Y) <=> true.
```

1. Fresh vars: TX, TY.
2. Head `qux(X)`: `copy_term([any], FT)` → FT = `[any]`.
   `tc_unify(TX, any, ctx)` → rule (3) → TX = any.
3. Head `foo(X, Y)`: `copy_term([α, α], FT)` → FT = `[α', α']`.
   `tc_unify(TX, α', ctx)` = `tc_unify(any, α', ctx)`.
   Rule (1): `nonvar(any)` true → succeed. **α' NOT bound.** ✓
   `tc_unify(TY, α', ctx)`: both vars → TY = α'.
4. Head `bar(Y)`: `copy_term([int], FT)` → FT = `[int]`.
   `tc_unify(TY, int, ctx)`: TY bound to α', deref → α' (var).
   Var rule → α' = int → TY = int.
5. **Result: no errors. Y is int, X is any. The type parameter α'
   became int despite X being any. ✓**

