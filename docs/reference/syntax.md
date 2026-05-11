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
| `:- chr_constraint Decls.` | Declare CHR constraints. |
| `:- chr_type T ---> Cs.` | Declare an algebraic type. |
| `:- function Decls.` | Declare a closed user-defined function. All decls (typed or untyped) and all equations must live in the declaring module; the decls must form a contiguous block of module items. |
| `:- open_function Decls.` | Declare an open user-defined function. Decls must still be in one module and contiguous, but other modules may contribute extension signatures via `:- extend_function_type` and extension equations via `:- extend_function`. |
| `:- extend_function_type (Name(Ts) -> T).` | Add an overloaded type signature to an open function declared elsewhere. The function name resolves through the importing module's imports. Targeting a closed function is an error (YCHR-16005). |
| `:- extend_function Name(Args) [\| Guards] -> Body.` | Add an equation to an open function declared elsewhere. Same scoping rules as `extend_function_type`. Free-floating equation syntax (`name(args) -> body.`) is only allowed in the declaring module of the function; appearing elsewhere is an error (YCHR-16006). |
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
