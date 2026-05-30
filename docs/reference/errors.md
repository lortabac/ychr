# Error Code Reference

> **Audience:** users hitting a `YCHR-NNNNN` diagnostic and looking up
> what it means.

YCHR diagnostics carry a numeric code of the form `YCHR-NNNNN`. The codes
are stable across releases; user-facing messages may evolve.

The source of truth lives in `src/YCHR/Display.hs`, which maps each
internal error constructor to its code and human-readable message.

## Catalog

### Collect phase (`1xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-10001` | `UnknownLibrary` | A `:- use_module(library(name))` directive names a library that is not bundled with the compiler. Check the spelling against the built-in library list. |
| `YCHR-10002` | `CircularLibraryImport` | The transitive `use_module(library(...))` graph contains a cycle. Break the cycle by removing or restructuring one of the imports. |

### Parse validation phase (`15xxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-15001` | `DiscontiguousEquations` | Equations for a function are not contiguous in the source. Group them together, or declare the function as `:- open_function` to allow extensions from other modules. |
| `YCHR-15002` | `MalformedImport` | A `use_module(...)` directive's argument is not a module name or `library(name)`. |
| `YCHR-15003` | `MalformedConstraint` | A `:- chr_constraint` declaration item is not an atom or compound term. |
| `YCHR-15004` | `DiscontiguousFunctionDecls` | Declarations for a name are not contiguous. Group them, or use the appropriate `:- extend_*` directive from another module. |
| `YCHR-15005` | `RequiringOnClass` | A `requiring` clause appears on `:- class` / `:- open_class`. Bounded polymorphism is reserved for `:- function` / `:- open_function`. |
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

### Rename phase (`2xxxx` errors, `2x1xx` warnings)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-20001` | `AmbiguousName` | A name is exported by multiple imported modules. Qualify it explicitly (`mod:name`) to disambiguate. |
| `YCHR-20002` | `UnknownName` | A name is not declared in this module and not imported from any other. Declare it with `:- chr_constraint` / `:- function`, or import it. |
| `YCHR-20003` | `UnknownExport` | A module exports a name that it does not declare. |
| `YCHR-20005` | `UnknownImport` | A `use_module(...)` import list names something the target module does not export. |
| `YCHR-20006` | `UnknownOperatorImport` | A `use_module(...)` import list names an operator that the target module does not export. |
| `YCHR-20007` | `UseModuleOutOfOrder` | A `use_module(...)` directive does not come immediately after `:- module(...)`. All imports must precede other directives and rules. |
| `YCHR-20008` | `UnknownExportedConstructor` | A `type(t/n, [c, ...])` export or import entry names a constructor that the type does not declare. Fix the typo, add the constructor to the type, or remove it from the list. |
| `YCHR-20009` | `NotExportedByModule` | A qualified reference targets a module that does not export the named item. Check the spelling and the exporter's export list. |
| `YCHR-20010` | `NonExportedConstructor` | A qualified reference like `palette:green` names a data constructor that is declared on the type but excluded by the exporting module's allowlist. Add the constructor to the exporter's `type(t/n, [...])` list, or use a different one. |
| `YCHR-20011` | `ConstructorNotExported` | A `use_module(palette, [type(col/0, [green])])` import lists a constructor that is declared on the type but excluded by the exporting module's allowlist. Same underlying condition as `YCHR-20010` but observed at the import site rather than at a use site. |
| `YCHR-20012` | `AmbiguousDataConstructor` | An unqualified data-constructor reference is exported by more than one imported module. Qualify the constructor (`mod:ctor`) to disambiguate, or narrow the import list. Parallel to `YCHR-20001` for functions/constraints; data constructors are not arity-overloadable, so the error names only the constructor and the modules that export it. |
| `YCHR-20013` | `GoalNotAConstraint` | `ychr run -g GOAL` was given a goal that is not a single declared constraint — a bare expression (`true`, `1 + 1`), an `is`/`=` form, a conjunction (`a, b`), a function call (`factorial(5)`), or an unknown name. Rewrite the goal as a `chr_constraint`-declared call (or wrap it in one) for the CLI, or use `ychr repl` for the broader goal syntax. |
| `YCHR-20101` | `UndeclaredDataConstructor` *(warning)* | A symbol used in constructor position is not declared with `:- chr_type`. Declare it, or check the spelling. |
| `YCHR-20102` | `DataConstructorArityMismatch` *(warning)* | A data constructor is used with a different arity than declared. |

### Desugar phase (`3xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-30001` | `UnexpectedBodyExpr` | An expression is not valid in a rule body. Rule bodies may contain constraints, function calls, unifications (`=`), `is` expressions, and `true`. |
| `YCHR-30002` | `NonBooleanGuard` | An expression that cannot evaluate to a boolean is used as a guard. Guards must be function calls, boolean-typed variables, `true`/`false`, or a host call returning a boolean. |

### Compile phase (`4xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-40001` | `UnknownConstraintType` | A reference to a constraint type that is not declared. Declare it with `:- chr_constraint name/arity`. |
| `YCHR-40002` | `UnboundVariable` | A variable used in a guard or body does not appear in the rule head. |

### Top-level errors (`5xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-50001` | parse error | The lexer or parser failed to recognize the input. The message includes parsec's expected/unexpected tokens. |
| `YCHR-50002` | `OperatorConflict` | An operator is declared with a fixity or associativity that conflicts with an existing declaration. Re-export the existing declaration instead of redeclaring it, or rename. |
| `YCHR-50003` | `LambdasInLiveQuery` | Anonymous lambdas (`fun(...) -> ... end`) appear in a live REPL session. Lift the lambda into a named `:- function` declaration in a file and reload the session. |

### Type-check phase (`6xxxx`)

| Code | Name | Meaning |
|------|------|---------|
| `YCHR-60001` | `InconsistentTypes` | Two types cannot be unified. Also used for runtime errors raised by the Haskell interpreter (e.g. arithmetic on non-numbers, calling a non-function). |
| `YCHR-60004` | `UnboundTypeVar` | A type variable used in a constructor declaration is not in scope. Add it to the parameter list of the enclosing type. |
| `YCHR-60005` | `UndefinedType` | A constructor declaration references a type that is not declared. Declare it with `:- chr_type`, or check the spelling. |
| `YCHR-60006` | `NoMatchingOverload` | No declared signature of a class matches the argument types at this use site. Check that the argument types match one of the declared signatures. |
| `YCHR-60007` | `DuplicateConstructor` | A data constructor is declared in multiple types. Rename one of them. |
| `YCHR-60008` | `ConstructorArityMismatch` | A data constructor is used with a different arity than declared. |
| `YCHR-60012` | `BoundUnsatisfied` | No declared signature of a bound function is consistent with the substituted bound at this use site. Either widen the bound function's overload set, or call the bounded operation at a type for which a signature exists. |

## See also

- [Language reference](language.md).
- [Type-system reference](type-system.md).
