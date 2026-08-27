# Error Code Reference

> **Audience:** users hitting a `YCHR-NNNNN` diagnostic and looking up
> what it means.

YCHR diagnostics carry a numeric code of the form `YCHR-NNNNN`. The codes
are stable across releases; user-facing messages may evolve.

The source of truth lives in `src/YCHR/Internal/Display.hs`, which maps each
internal error constructor to its code and human-readable message.

## Catalog

### Collect phase (`1xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-10001` | `UnknownLibrary` | A `:- use_module(library(name))` directive names a library that is not bundled with the compiler. Check the spelling against the built-in library list. |
| `YCHR-10002` | `CircularLibraryImport` | The transitive `use_module(library(...))` graph contains a cycle. Break the cycle by removing or restructuring one of the imports. |
| `YCHR-10003` | `SelfNamedLibraryImport` | A module named `N` writes `:- use_module(library(N))`. Modules are identified by name, so this module replaces the bundled library and the import names the module itself — it can bring nothing into scope. Rename the module, or drop the import. |

### Parse validation phase (`15xxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-15001` | `DiscontiguousEquations` | Equations for a function are not contiguous in the source. Group them together, or declare the function as `:- open_function` to allow extensions from other modules. |
| `YCHR-15002` | `MalformedImport` | A `use_module(...)` directive's argument is not a module name or `library(name)`. |
| `YCHR-15003` | `MalformedConstraint` | A rule head or a query goal contains something that is not an atom or compound term (a bare variable, integer, or string). A malformed `:- chr_constraint` *declaration* item is `YCHR-15007` instead. |
| `YCHR-15004` | `DiscontiguousFunctionDecls` | Declarations for a name are not contiguous. Group them, or use the appropriate `:- extend_*` directive from another module. |
| `YCHR-15005` | `RequiringOnClass` | A `requiring` clause appears on `:- class` / `:- open_class`. Bounded polymorphism belongs on `:- function` / `:- open_function` / `:- chr_constraint`, never on the class forms. |
| `YCHR-15006` | `RequiringOnExtendClassType` | A `requiring` clause appears on `:- extend_class_type`. Bounds belong to the original declaration; extensions cannot introduce them. |
| `YCHR-15007` | `MalformedDeclaration` | A declaration is not `name/arity`, `name(types) -> ret`, or `sig requiring bounds`. |
| `YCHR-15008` | `MalformedExportItem` | An export/import list item is not `name/arity`, `fun name/arity`, `type(name/arity)`, or `op(prio, type, name)`. |
| `YCHR-15009` | `MalformedTypeExpr` | A type expression is not a type variable, atom, or compound type. |
| `YCHR-15010` | `MalformedDataConstructor` | A `chr_type` alternative is not an atom or compound term. |
| `YCHR-15011` | `MalformedTypeDefinition` | A type definition does not match `name(Vars) ---> con1 ; con2 ; ...`. |
| `YCHR-15012` | `MalformedBoundSig` | A bound signature is not `name(t1, ..., tn) -> tret` (or `name -> tret` for arity zero). |
| `YCHR-15013` | `MalformedFunctionEquation` | A function equation is not `lhs [\| guard] -> rhs`. |
| `YCHR-15014` | `MalformedTopLevel` | A top-level term is not a directive, rule (`<=>` or `==>`), or function equation (`->`). |
| `YCHR-15015` | `DuplicateModuleHeader` | A source file contains more than one `:- module(...)` directive. A file may declare at most one module header; remove the redundant directives. |
| `YCHR-15016` | `OpaqueTypeHasConstructors` | A `:- opaque_type` directive carries a constructor body (`---> ...`). Opaque types have no data constructors; use `:- chr_type` for a type with constructors. |
| `YCHR-15017` | `MalformedOpaqueTypeDefinition` | A `:- opaque_type` directive is not `name` or `name(Vars)`. |
| `YCHR-15018` | `InvalidTypeParameter` | A type-definition parameter (in `:- chr_type` or `:- opaque_type`) is not a type variable. The anonymous variable `_` is rejected too — a parameter has to be nameable to be referred to in a constructor field. |
| `YCHR-15019` | `DuplicateTypeParameter` | The same variable appears more than once in a type definition's parameter list. |

### Resolve phase (`16xxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-16001` | `ConstraintHasEquations` | A name is declared as `:- chr_constraint` but has function equations (`->`). Either declare it as a function or remove the equations. |
| `YCHR-16002` | `FunctionInRuleHead` | A function name appears in a rule head. Rule heads must be constraints; call the function from the body or a guard. |
| `YCHR-16003` | `ReservedName` | A reserved name is used as a constraint or function. |
| `YCHR-16004` | `UnqualifiedConstraintName` | Internal error: an unqualified constraint name reached the resolve phase. Report it as a YCHR bug. |
| `YCHR-16005` | `ExtendsClosedFunction` | An `:- extend_function` / `:- extend_class_type` / `:- extend_class` targets a closed declaration. Declare the target as `:- open_function` or `:- open_class`. |
| `YCHR-16006` | `OrphanFunctionEquation` | A free-floating equation (`name(args) -> body.`) appears outside the declaring module. Use `:- extend_function` / `:- extend_class` instead. |
| `YCHR-16007` | `ExtendTypeOnBoundedFunction` | `:- extend_class_type` targets a bounded open function. The instance set of a bounded open function is determined by its `requiring` clause; declare a new signature of the bound function instead. |
| `YCHR-16008` | `UnboundBoundVariable` | A type variable in a `requiring` clause does not appear in the declaration's primary signature. Every variable in `requiring` must also appear in the argument or return types. |
| `YCHR-16009` | `UnknownBoundFunction` | A `requiring` clause names a function that is not declared. Declare it with `:- function`, or import a module that does. |
| `YCHR-16010` | `BoundCycle` | The `requiring` graph contains a cycle. The bound graph must be acyclic. |
| `YCHR-16011` | `MultiSigOnFunction` | A `:- function` / `:- open_function` declaration has multiple signatures. Use `:- class` / `:- open_class` for signature overloading, or keep a single signature. |
| `YCHR-16012` | `MixedDeclKinds` | A name is declared with both `:- function` and `:- class` forms. Pick one form. |
| `YCHR-16013` | `ExtendClassTypeOnFunction` | `:- extend_class_type` targets a name declared as `:- open_function`. Type extensions are only meaningful on `:- open_class`. |
| `YCHR-16014` | `ExtendClassOnFunction` | `:- extend_class` targets a name declared as `:- open_function`. Use `:- extend_function` instead. |
| `YCHR-16015` | `ExtendFunctionOnClass` | `:- extend_function` targets a name declared as `:- open_class`. Use `:- extend_class` instead. |
| `YCHR-16016` | `ConstraintFunctionCollision` | A name is declared as both `:- chr_constraint` and a function-like form in the same module. Constraints and functions share the symbol namespace. |
| `YCHR-16017` | `LambdaParamError` | A lambda parameter is not a variable or the anonymous variable (`_`). |
| `YCHR-16018` | `EmptyLambdaParams` | A lambda has no parameters. Lambdas must declare at least one parameter; use `:- function` for a no-arg helper. |
| `YCHR-16019` | `ReservedModuleName` | A user module is declared with a reserved name (currently `host`, which is wired in as the host-call qualifier). Rename the module. |
| `YCHR-16020` | `ConstructorFunctionCollision` | The same name is declared as a data constructor (`:- chr_type`) and as a function-like form in one module. Both spell as `mod:name`, so qualifying a reference cannot say which is meant. Arity does not separate them either — constructors are name-only in the type system — so `foo/0` the constructor collides with `foo/1` the function. Rename one of them. The cross-module version of this clash is legal and is reported per bare use as `YCHR-20020`. |

### Rename phase (`2xxxx` errors) and program warnings (`2x1xx`)

The warning codes share the `2xxxx` block but not the phase: `20101`
and `20102` come from renaming, `20103` from the exhaustiveness pass,
and `20104` from the type checker. Every `--Werror`-eligible
diagnostic carries a `2x1xx` code.

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-20001` | `AmbiguousName` | A name is exported by multiple imported modules. Qualify it explicitly (`mod:name`) to disambiguate. |
| `YCHR-20002` | `UnknownName` | A name is not declared in this module and not imported from any other. Declare it with `:- chr_constraint` / `:- function`, or import it. |
| `YCHR-20003` | `UnknownExport` | A module exports a name that it does not declare. |
| `YCHR-20005` | `UnknownImport` | A `use_module(...)` import list names something the target module does not export. |
| `YCHR-20006` | `UnknownOperatorImport` | A `use_module(...)` import list names an operator that the target module does not export. |
| `YCHR-20007` | `UseModuleOutOfOrder` | A `use_module(...)` directive does not come immediately after `:- module(...)`. All imports must precede other directives and rules. |
| `YCHR-20008` | `UnknownExportedConstructor` | A `type(t/n, [c, ...])` export or import entry names a constructor that the type does not declare. Fix the typo, add the constructor to the type, or remove it from the list. |
| `YCHR-20009` | `NotExportedByModule` | A qualified reference targets a module that *is imported* but does not export the named item (or a restricted import list excludes it). Check the spelling and the exporter's export list. For the not-imported and non-existent cases see `YCHR-20014` and `YCHR-20015`. |
| `YCHR-20010` | `NonExportedConstructor` | A qualified reference like `palette:green` names a data constructor that is declared on the type but excluded by the exporting module's allowlist. Add the constructor to the exporter's `type(t/n, [...])` list, or use a different one. |
| `YCHR-20011` | `ConstructorNotExported` | A `use_module(palette, [type(col/0, [green])])` import lists a constructor that is declared on the type but excluded by the exporting module's allowlist. Same underlying condition as `YCHR-20010` but observed at the import site rather than at a use site. |
| `YCHR-20012` | `AmbiguousDataConstructor` | An unqualified data-constructor reference is exported by more than one imported module. Qualify the constructor (`mod:ctor`) to disambiguate, or narrow the import list — except when one of the clashing modules is the prelude, whose import cannot be narrowed (`YCHR-20019`); rename your own constructor instead. Parallel to `YCHR-20001` for functions/constraints; data constructors are not arity-overloadable, so the error names only the constructor and the modules that export it. |
| `YCHR-20013` | `GoalNotAConstraint` | `ychr run -g GOAL` was given a goal that is not a single declared constraint — a bare expression (`true`, `1 + 1`), an `is`/`=` form, a conjunction (`a, b`), a function call (`factorial(5)`), or an unknown name. Also reported when the name is ambiguous (exported by more than one imported module — qualify it) or when its module declares it without exporting it. Rewrite the goal as a `chr_constraint`-declared call (or wrap it in one) for the CLI, or use `ychr repl` for the broader goal syntax. |
| `YCHR-20014` | `ModuleNotImported` | A qualified reference `m:name` targets a module `m` that exists in the program but the current module never imports. Qualifying a name does not bypass the import requirement — add `:- use_module(m).`. |
| `YCHR-20015` | `UnknownModule` | A qualified reference `m:name` targets a module `m` that does not exist anywhere in the program. Check the module name, or declare/supply the module. |
| `YCHR-20016` | `ReservedTypeName` | A `:- chr_type` / `:- opaque_type` declaration redeclares a reserved type name: a base type (`int`, `float`, `string`, `any`) or function-type syntax (`fun`, `->`). The latter two only reach this check when quoted (`'fun'`, `'->'`); written bare they are reserved syntax and fail earlier, as `YCHR-50001`. |
| `YCHR-20017` | `DuplicateTypeDeclaration` | The same type name and arity is declared more than once in one module. |
| `YCHR-20018` | `TypeShadowsImport` | A type declaration collides with a type of the same name and arity visible through an import. |
| `YCHR-20019` | `PreludeImportList` | A `use_module(...)` directive targeting the prelude carries an import list. The prelude is imported implicitly and in full by every module, so the list has no effect — remove it. The unrestricted forms `:- use_module(prelude).` and `:- use_module(library(prelude)).` are accepted (and redundant). |
| `YCHR-20020` | `ConstructorFunctionAmbiguity` | A bare reference names something that is visible both as a data constructor and as a function. Without this check the two would be told apart by syntactic position — pattern positions take the constructor, evaluating positions take the function — so the same text would mean different things in different parts of one rule. Arity is not part of the comparison. Qualify the reference (`mod:name`) to say which you mean, or rename one of them; the prelude's import cannot be narrowed, so rename your own constructor when the clash is with the prelude. Parallel to `YCHR-20012`, which is the same question within the constructor namespace alone. |
| `YCHR-20101` | `UndeclaredDataConstructor` *(warning)* | A symbol used in constructor position is not declared with `:- chr_type`. Declare it, or check the spelling. |
| `YCHR-20102` | `DataConstructorArityMismatch` *(warning)* | A data constructor is used with a different arity than declared. Comes from the renamer, so it does not depend on the type checker; the type checker reports the same mistake as `YCHR-60008`, naming the declared arity. One wrong use draws both. |
| `YCHR-20103` | `NonExhaustiveMatch` *(warning)* | A function's equations do not cover every constructor of an argument's algebraic type; the message names a concrete unmatched example. Add an equation for the missing case, or a catch-all variable/wildcard pattern. The check is deliberately narrow — closed single-signature functions only, arguments of algebraic type only, and a guarded equation does not count as covering its pattern. See [the type-system reference](type-system.md) §Exhaustiveness checking for the full conditions. |
| `YCHR-20104` | `InaccessibleBranch` *(warning)* | A rule or equation can never fire: the typing fact a guard's success would entail contradicts what is already known, so the guard cannot succeed in the typed fragment. Covers a type predicate against a known type (`integer(X)` where `X` is typed `color`), a constructor match against a type that has no such constructor, and an equality with no solution at all (matching `f(X, X)` against `:- function f(T, list(T)) -> ...`). Remove the dead rule or fix the type it disagrees with. Reported only when the rule or equation otherwise checks clean — an error in the same rule or equation is reported instead. Specified in [the type-system reference](type-system.md). |

### Desugar phase (`3xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-30001` | `UnexpectedBodyExpr` | An expression is not valid in a rule body. Rule bodies may contain constraints, function calls, unifications (`=`), `is` expressions, and `true`. |
| `YCHR-30002` | `NonBooleanGuard` | An expression that cannot evaluate to a boolean is used as a guard. Guards must be function calls, boolean-typed variables, `true`/`false`, or a host call returning a boolean. |
| `YCHR-30003` | `NonPreludeFunctionBodyItem` | A non-final item in a sequenced function body is not one of the permitted forms. Only `X is E`, a host call `host:f(...)`, a function call `f(...)`, and `'$call'(F, ...)` may precede the return expression. |
| `YCHR-30004` | `NonVariableIsInFunctionBody` | The left-hand side of an `is` in a function body is not a variable. Function bodies have no unification machinery, so `is` can only bind a fresh name. |

### Compile phase (`4xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-40001` | `UnknownConstraintType` | A reference to a constraint type that is not declared. Declare it with `:- chr_constraint name/arity`. |
| `YCHR-40002` | `UnboundVariable` | A variable used in a guard or body does not appear in the rule head — or, for a function equation, in its parameters. |

### Top-level errors (`5xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-50001` | parse error | The lexer or parser failed to recognize the input. The message includes parsec's expected/unexpected tokens. |
| `YCHR-50002` | `OperatorConflict` | An operator is declared with a fixity or associativity that conflicts with an existing declaration. Re-export the existing declaration instead of redeclaring it, or rename. |
| `YCHR-50003` | `LambdasInLiveQuery` | Anonymous lambdas (`fun(...) -> ... end`) appear in a live REPL session. Lift the lambda into a named `:- function` declaration in a file and reload the session. |

### Type-check phase (`6xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-60001` | `InconsistentTypes` | Two types cannot be unified. Also used for runtime errors raised by the Haskell interpreter (e.g. arithmetic on non-numbers, calling a non-function, a guard not evaluating to a boolean). |
| `YCHR-60004` | `UnboundTypeVar` | A type variable used in a constructor declaration is not in scope. Add it to the parameter list of the enclosing type. |
| `YCHR-60005` | `UndefinedType` | A constructor declaration references a type that is not declared. Declare it with `:- chr_type`, or check the spelling. |
| `YCHR-60006` | `NoMatchingOverload` | No declared signature of a class matches the argument types at this use site. Check that the argument types match one of the declared signatures. Also reported when the use site is inside a polymorphic declaration and the argument is one of its own type variables (`:- function f(T, T) -> bool.` with a body calling `>`): inside its own declaration a type variable is only consistent with itself and `any`, so no signature of `>` matches — add a `requiring` clause naming the operation, or a signature for a concrete type. Equally, an equation of a `:- class` that checks under none of its declared signatures. |
| `YCHR-60007` | `DuplicateConstructor` | A data constructor is declared in multiple types. Rename one of them. |
| `YCHR-60008` | `ConstructorArityMismatch` | A data constructor is used with a different arity than declared. The type-checker's counterpart to the renamer's `YCHR-20102` warning; this one names the declared arity, and the wrong-arity use is typed `any` rather than drawing a second, downstream mismatch. |
| `YCHR-60012` | `BoundUnsatisfied` | No declared signature of a bound function is consistent with the substituted bound at this use site. Either widen the bound function's overload set, or call the bounded operation at a type for which a signature exists. |
| `YCHR-60013` | `TypeRefArityMismatch` | A constructor field references a type constructor applied to a different number of arguments than its declaration has parameters (base types have zero). |

## See also

- [Language reference](language.md).
- [Type-system reference](type-system.md).
