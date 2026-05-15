# Syntax Reference

> **Audience:** anyone writing or reading YCHR source.

This page is a stub. The eventual reference will cover:

## Lexical syntax

- **Comments.** `% line comment`. Block comments? **TODO.**
- **Whitespace.** Treated uniformly between tokens.
- **Identifiers.** Atoms (lowercase-leading or quoted), variables
  (uppercase- or `_`-leading), wildcards (`_`), module separators (`:`).
- **Number literals.** Integers (incl. negative), floats. **TODO:** full
  grammar including underscores, exponents, hex.
- **String literals.** Double-quoted; escape sequences. **TODO.**
- **Quoted atoms.** `'...'` for atoms containing punctuation; escape
  sequences. **TODO.**

## Operators

- `op(Priority, Type, Name)` directives, as in standard Prolog.
- The default operator table is defined in `libraries/prelude.chr`.

> **TODO:** full table of built-in operators with priorities, types, and
> meanings.

## Directives

| Directive | Purpose |
|-----------|---------|
| `:- module(Name, Exports).` | Module header with explicit export list. Each entry is `name/arity`, `fun(name/arity)`, `op(Pri, Type, Name)`, `type(name/arity)`, or `type(name/arity, [Con, ...])`. |
| `:- module(Name).` | Module header that exports every declared identifier. |
| `:- use_module(M)` / `:- use_module(M, Imports).` | Import another module. Import items use the same forms as export items. |
| `type(name/arity, [Con1, ...])` | Two-argument type form. Exports (or imports) the type and only the listed data constructors; `type(name/arity)` covers all of them. |
| `:- chr_constraint Decls.` | Declare CHR constraints. A name+arity declared here cannot also be declared as a function-like form (`:- function`, `:- open_function`, `:- class`, `:- open_class`) in the same module (YCHR-16016). |
| `:- chr_type T ---> Cs.` | Declare an algebraic type. |
| `:- function Decls.` | Declare a closed user-defined function. Single signature only — multi-signature requires `:- class` (YCHR-16011). All decls (typed or untyped) and all equations must live in the declaring module; the decls must form a contiguous block of module items. May carry a `requiring` clause (bounded polymorphism). |
| `:- open_function Decls.` | Declare an open user-defined function. Single signature only. Decls must still be in one module and contiguous, but other modules may contribute extension equations via `:- extend_function`. Type-signature extension is not available (see `:- open_class`). |
| `:- class Decls.` | Declare a closed user-defined class. Like `:- function`, but enables multi-signature overloading: two or more typed signatures for the same name and arity. `requiring` is forbidden on `:- class` (YCHR-15005); bounded polymorphism is reserved for `:- function` / `:- open_function`. |
| `:- open_class Decls.` | Declare an open user-defined class. Other modules may contribute extension signatures via `:- extend_class_type` and extension equations via `:- extend_class`. |
| `:- extend_class_type (Name(Ts) -> T).` | Add an overloaded type signature to an `:- open_class` declared elsewhere. The class name resolves through the importing module's imports. Targeting a closed declaration is an error (YCHR-16005); targeting an `:- open_function` is `ExtendClassTypeOnFunction` (YCHR-16013). |
| `:- extend_function Name(Args) [\| Guards] -> Body.` | Add an equation to an `:- open_function` declared elsewhere. Targeting an `:- open_class` is `ExtendFunctionOnClass` (YCHR-16015). Free-floating equation syntax (`name(args) -> body.`) is only allowed in the declaring module; appearing elsewhere is an error (YCHR-16006). |
| `:- extend_class Name(Args) [\| Guards] -> Body.` | Add an equation to an `:- open_class` declared elsewhere. Targeting an `:- open_function` is `ExtendClassOnFunction` (YCHR-16014). |
| `:- discontiguous Names.` | Allow equations of the same function to be split. |
| `:- op(Pri, Type, Name).` | Declare an operator. |

## Rules

| Operator | Kind |
|----------|------|
| `<=>` | Simplification rule. |
| `==>` | Propagation rule. |
| `\` | Simpagation separator (kept `\` removed). |

> **TODO:** rule head grammar (constraints separated by `,`), guard
> separator `|`, body separator after `<=>`/`==>`, optional rule names
> with `Name @ ...`.

## Expressions

> **TODO:** functor application, lists, lambdas (`fun(X) -> E end`),
> function references (`fun name/arity`), `is` expressions, `=` and `==`,
> guard syntax.

## See also

- [Language reference](language.md) — feature-level description.
- [Type system](type-system.md) — typing rules over the syntax.
