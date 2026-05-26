# Syntax Reference

> **Audience:** anyone writing or reading YCHR source.
> **You will:** find the lexical rules, the directive table, the rule
> grammar, and the expression forms accepted by the parser.

For *why* the language looks the way it does — the points where YCHR
diverges from K.U.Leuven CHR — see [language.md](language.md). For
typing rules over this syntax see [type-system.md](type-system.md).

## Lexical syntax

- **Comments.** `% line comment` to end of line. There are no block
  comments.
- **Whitespace.** Treated uniformly between tokens.
- **Identifiers and atoms.**
  - **Unquoted atoms** start with a lowercase letter and continue with
    letters, digits, or underscores. Double underscore `__` is not
    allowed (reserved as the qualified-name separator in compiled
    output). Identifiers that are prefix word operators
    (`chr_constraint`, `function`, `class`, …) cannot be used as bare
    atoms; quote them if you need the literal name.
  - **Quoted atoms** are written `'…'`. Inside the quotes, `''`
    encodes a literal single quote (ISO Prolog convention), and the
    backslash escapes `\\`, `\'`, `\n`, `\t` are recognized. Any other
    `\c` falls through to the literal `c`.
  - **Variables** start with an uppercase letter or underscore, then
    letters, digits, or underscores. The bare `_` is the wildcard:
    distinct occurrences are independent.
- **Number literals.**
  - Integers: a decimal digit sequence, optionally preceded by `-`.
    Arbitrary precision; there is no upper or lower bound. No
    underscore separators, no hexadecimal / octal / binary notation.
  - Floats: an integer part, a `.`, and at least one fractional
    digit, optionally preceded by `-`. No exponent syntax.
- **String literals.** Double-quoted: `"…"`. Recognized escapes are
  `\"`, `\\`, `\n`, `\t`; any other `\c` falls through to the literal
  `c`. Strings are values of type `string`, *not* code lists.
- **Module separator.** `:` separates a module name from a name it
  qualifies (e.g. `lists:append`).
- **List sugar.** `[]`, `[a, b, c]`, and `[H | T]` desugar to the
  standard `'.'/2` cons-cell representation.

## Operators

Operator precedences and associativities follow standard Prolog
conventions and are exposed through `op/3`. Two notes specific to
YCHR:

- The default operator table is composed of a small built-in core
  (the directive keywords, `=`, `is`, the rule operators, the bounded
  polymorphism `requiring`, …) extended with the operators declared
  in `libraries/prelude.chr`. The prelude is implicitly imported, so
  arithmetic and comparison operators are always in scope.
- `is` and `=` sit at priority 750 (not the Prolog default 700) so
  that comparisons may appear unparenthesized on the right-hand side.
  See [language.md](language.md#the-is-operator).

User code declares its own operators with `op(Priority, Type, Name)`
entries inside a `:- module(...)` export list or a `:- use_module(M, ...)`
import list. There is no top-level `:- op(...)` directive.

The REPL will eventually grow an operator-introspection command; until
then, the authoritative list of in-scope operators is whatever appears
in `libraries/prelude.chr` plus the user modules.

## Directives

| Directive | Purpose |
|-----------|---------|
| `:- module(Name, Exports).` | *Optional* module header with explicit export list. Each entry is `name/arity`, `fun name/arity`, `op(Pri, Type, Name)`, `type(name/arity)`, or `type(name/arity, [Con, ...])`. |
| `:- module(Name).` | *Optional* module header that exports every constraint, function, type, and operator declared in the module. A file with no header forms an unnamed module with the same export semantics; diagnostics refer to it by its file basename (e.g. `<a>` for `a.chr`). |
| `:- use_module(M)` / `:- use_module(M, Imports).` | Import another module. Import items use the same forms as export items. The wrapper `library(Name)` is accepted as a synonym for a bare module name. All `use_module` directives must appear before the first non-import directive or rule in the file (YCHR-20007). |
| `type(name/arity, [Con1, ...])` | Two-argument type form. Exports (or imports) the type and only the listed data constructors; `type(name/arity)` covers all of them. The arity is the number of *type parameters*. |
| `:- chr_constraint Decls.` | Declare CHR constraints. Each `Decl` is `name/arity` (untyped) or `name(τ₁, ..., τₙ)` (typed; arity inferred). May carry a `requiring` clause when typed. A name+arity declared here cannot also be declared as a function-like form (`:- function`, `:- open_function`, `:- class`, `:- open_class`) in the same module (YCHR-16016). |
| `:- chr_type T ---> Cs.` | Declare an algebraic type with named constructors. |
| `:- function Decls.` | Declare a closed user-defined function. Single signature only — multi-signature requires `:- class` (YCHR-16011). All decls (typed or untyped) and all equations must live in the declaring module; the decls must form a contiguous block of module items (YCHR-15004) and the equations a contiguous block (YCHR-15001). May carry a `requiring` clause (bounded polymorphism). |
| `:- open_function Decls.` | Declare an open user-defined function. Single signature only. Decls must still be in one module and contiguous, but other modules may contribute extension equations via `:- extend_function`. Type-signature extension is not available (see `:- open_class`). |
| `:- class Decls.` | Declare a closed user-defined class. Like `:- function`, but enables multi-signature overloading: two or more typed signatures for the same name and arity. `requiring` is forbidden on `:- class` (YCHR-15005); bounded polymorphism is reserved for `:- function` / `:- open_function`. |
| `:- open_class Decls.` | Declare an open user-defined class. Other modules may contribute extension signatures via `:- extend_class_type` and extension equations via `:- extend_class`. |
| `:- extend_class_type (Name(Ts) -> T).` | Add an overloaded type signature to an `:- open_class` declared elsewhere. The class name resolves through the importing module's imports. Targeting a closed declaration is an error (YCHR-16005); targeting an `:- open_function` is `ExtendClassTypeOnFunction` (YCHR-16013). |
| `:- extend_function Name(Args) [\| Guards] -> Body.` | Add an equation to an `:- open_function` declared elsewhere. Targeting an `:- open_class` is `ExtendFunctionOnClass` (YCHR-16015). Free-floating equation syntax (`name(args) -> body.`) is only allowed in the declaring module; appearing elsewhere is an error (YCHR-16006). |
| `:- extend_class Name(Args) [\| Guards] -> Body.` | Add an equation to an `:- open_class` declared elsewhere. Targeting an `:- open_function` is `ExtendClassOnFunction` (YCHR-16014). |

All declaration directives accept a comma-separated list. For example,
`:- chr_constraint fib/2, upto/1.` declares two constraints in one
directive.

Unknown directives (any `:- foo(...)` not in this table) are silently
dropped at parse time. This is meant for Prolog-source compatibility,
not as an extension point.

## Rules

Rules have the form

```
[Name @] Head <=> [Guard |] Body.
[Name @] Head ==> [Guard |] Body.
[Name @] Kept \ Removed <=> [Guard |] Body.
```

| Operator | Kind |
|----------|------|
| `<=>` | Simplification rule. |
| `==>` | Propagation rule. |
| `\` (inside a head) | Simpagation separator: `Kept \ Removed`. |
| `@` | Rule-name separator (atom `@` head). The name is optional. |
| `|` (in the head/body split) | Guard separator. |
| `,` | Conjunction in head, guard, and body. |

`Head`, `Removed`, and `Kept` are comma-separated lists of constraint
applications. `Guard` is a comma-separated list of boolean
expressions evaluated with ask semantics (no variable binding); see
[language.md §Tell-side evaluation](language.md#tell-side-evaluation).
`Body` is a comma-separated list of constraints to tell.

## Function equations

Function equations have the form

```
Name(Args) [| Guards] -> Body.
```

`Body` is either a single expression or a comma-separated sequence
`Item1, Item2, ..., Return` where `Return` is an expression and each
earlier `Item` is one of: `X is E` (variable LHS only), `host:f(args)`,
a function call `f(args)`, or `'$call'(F, args)`. Lambdas
(`fun(X) -> Body end`) accept the same body forms. Anything else in a
non-final position is rejected — see [language.md §Sequencing in
function bodies](language.md#sequencing-in-function-bodies).

## Expressions

Every expression position parses the same surface terms; the *kind*
of expression is decided structurally during resolution
([language.md](language.md#tell-side-evaluation) covers when a term
evaluates).

| Form | Meaning |
|------|---------|
| `42`, `-3`, `3.14` | Number literals. |
| `"text"` | String literal. |
| `foo`, `'a-b'` | Atom literal. |
| `X`, `_Tail` | Variable. `_` is the wildcard. |
| `f(A, B)` | Compound application. Becomes a function call, a constructor, or a tell-side constraint depending on what `f` resolves to. |
| `[a, b]`, `[H | T]`, `[]` | List, list with tail, empty list. |
| `M:name`, `M:name(A)` | Module-qualified reference. |
| `host:name(A)` | Host-language call (see [language.md §Host calls](language.md#host-calls)). |
| `term(E)` | Quote `E` as a data term (see [language.md §Tell-side evaluation](language.md#tell-side-evaluation)). |
| `fun(X, Y) -> Body end` | Lambda (anonymous function). Takes one or more parameters, each a variable or wildcard. |
| `fun name/arity` | Function reference (first-class value). |
| `'$call'(F, A1, A2)` | Wired-in dynamic-dispatch primitive. Prefer the prelude's typed `call/N` wrapper. |
| `X is E`, `X = E`, `A == B` | Evaluation, unification (tell), structural equality (ask). |

## See also

- [Language reference](language.md) — feature-level description and
  semantic divergences from standard CHR.
- [Type system](type-system.md) — typing rules over this syntax.
- [Prelude reference](prelude.md) — the auto-imported module that
  supplies arithmetic, comparison, type-predicate, and call-wrapper
  identifiers.
