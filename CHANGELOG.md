# Revision history for ychr

## Unreleased

Type-checker fixes aligning the implementation with the
[type-system specification](docs/reference/type-system.md):

- `any` never binds a type variable. A variable is typed `any` only
  when its declaration positions say so, judged over all sources at
  once — multi-source head typing no longer depends on head order,
  and `any` no longer leaks through shared variables.
- `R is e` types its RHS by evaluation (previously `is` was typed
  identically to `=`) and meets the result with the LHS through the
  ordinary meet table. It has no special power over `any`: an
  `any`-typed LHS is checked against and stays `any`, in rule bodies
  and function bodies alike.
- The operands of `=` are typed structurally, matching the runtime's
  structural unification: an evaluable-headed compound under `=` is
  a symbolic term typed `any`, not a function call. `Sum = 1 + 1` no
  longer types `Sum` as `int` (the runtime binds a symbolic
  compound); use `is` for the arithmetic — and the type.
- Equation bodies of untyped functions are now type-checked, exactly
  like their all-`any` spelled-out form. Programs with ill-typed
  bodies hiding behind untyped declarations may now be rejected
  (YCHR-60006) where they previously failed only at runtime.
- A polymorphic declaration's own type variables are now opaque inside
  its implementation — in a function's equations, and in a rule whose
  head mentions a polymorphic constraint (freshly per head occurrence,
  since the store may hold any mix of instances). Code that silently
  assumed one instantiation is now rejected: calling an overloaded
  operation at your own type variable needs a `requiring` clause, and
  two head occurrences of `leq(T, T)` no longer assume the same `T`
  unless a shared variable says so.
- Guard-derived type evidence: a guard whose success entails a typing
  fact — a type predicate (`integer(X)`), a constructor pattern, a
  repeated or literal head argument — contributes that fact to the
  positions that run after it. Evidence can only accept more programs;
  it enables operations at a type variable the guard has pinned, and
  is inert at `any` and at unconstrained variables.
- New warning **YCHR-20104** (inaccessible branch): a rule or equation
  whose guard contradicts a known type can never fire. Like the other
  `2x1xx` warnings it is promoted to an error by `--Werror`, and it is
  suppressed for a rule or equation that already reports an error.
- Overload resolution and `requiring` discharge are now residual: they
  stay pending and retry as inference adds information, instead of
  committing on first sight. A resolution still ambiguous when checking
  ends succeeds silently, as the specification requires. Each equation
  of a `:- class` is checked against every declared signature and needs
  to fit at least one.
- Declaration validation, with new codes: `YCHR-15018` (a type
  parameter that is not a type variable — previously dropped silently,
  changing the type's arity), `YCHR-15019` (a repeated type parameter),
  `YCHR-20016` (redeclaring a reserved type name such as `int`),
  `YCHR-20017` (a duplicate type declaration), `YCHR-20018` (a type
  declaration shadowing an imported one), and `YCHR-60013` (a
  constructor field applying a type constructor at the wrong arity).
- Arity-overloaded constraints and functions are keyed by name *and*
  arity throughout the checker; a `c/1` declaration no longer shadows
  `c/2`, which previously lost both `any` stamping and use-site
  checking for the shadowed arity.
- Lambda parameters shadow same-named enclosing variables, matching
  what the lambda lifter does at runtime.
- `Warning` (from `YCHR.Run`) gained a `TypeCheckWarnings` constructor.
  Code pattern-matching exhaustively on `Warning` needs a new case.

- A declared `any` nested inside a type now merges across a shared
  variable the way a top-level one does. With `p(list(any))` and
  `q(list(int))`, the rule `p(X), q(X) <=> ...` types `X` as
  `list(int)` — previously only `q(X), p(X)` did, and the other order
  silently kept `list(any)`, accepting whatever the body did with it.
  Programs relying on the accepting order may now report a type error.
  A position every declaration source leaves `any` still stays
  dynamic.
- A type that contains itself no longer hangs the compiler. Programs
  like `p(bx(W)) <=> W = bx(W)`, or the goal `p([X|X])`, made the
  checker bind a type variable to a type containing it; the resulting
  cyclic term wedged the next traversal. Such a fact now binds nothing
  and the program is accepted, as before.

Runtime:

- Unification now transfers a bound variable's observers onto the
  variables that binding made reachable, so a constraint waiting on
  `X` still wakes when `X` is bound to a term and *that* term's
  variable is bound later. Affects the Haskell runtime; the Scheme
  runtime still registers observers at store time only.

## 0.1.0.0 -- 2026-08-02

First release. See the
[README](https://github.com/lortabac/ychr#readme) for an overview and
[`docs/`](https://github.com/lortabac/ychr/tree/master/docs) for the
documentation.
