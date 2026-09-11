# Revision history for ychr

## Unreleased

New: opt-in search, `library(search)`. Explore alternative bindings and
undo the ones that do not work out. Nothing here affects a program that
does not import it, and there are no new VM instructions; the Haskell
runtime is the only backend that implements it. See the
[search specification](docs/reference/search.md).

- The primitive is `alt/1`, an ordinary CHR constraint with no rules.
  Telling it leaves it in the store; at quiescence the driver takes the
  oldest live one and tries its goals in list order, undoing the branch
  between attempts. An alternative is a *goal*, not a value, so a
  choice is between computations.
- The disjunction operator `;` is surface syntax for an `alt`, `xfy`
  at priority 1100, and is available in a rule body once the module
  imports `library(search)`. Each disjunct is lifted into its own
  constraint, the way a lambda is lifted. Choice is still made at
  quiescence, so in `p, (a ; b), q` the goal `q` is told before a
  branch is picked.
- `choose(X, Alts)` labels a variable and is one library rule over
  `alt/1` and `try_unify/2`, not a runtime primitive.
- Solutions are fetched with `solve/1` (first solution, bindings
  kept), `find_all/2` (all of them, everything undone) or
  `fold_solutions/4`, a fold over the solution sequence with early
  exit. `forall/3` and `find_n/3` are derived over the fold; `find_n`
  terminates on an infinite space, where `find_all` would not.
- `fail/0` abandons a branch, and `try_unify/2` is Prolog's `=`:
  unify, or fail rather than raise.
- Three new error codes: `YCHR-20021` (`;` without importing
  `library(search)`), `YCHR-20022` (`;` outside a rule body — in a
  guard, an `is` right-hand side or a function body) and `YCHR-30006`
  (`;` at the top level of a query).
- A `quote/1` argument in a *tell* position may now introduce a fresh
  variable, as an `=` operand may. An unbound name in an `is`
  right-hand side or a call argument is still `YCHR-40002`.
- The type checker's resolution of overloaded class-function
  signatures now runs on this library — one `solve/1` per equation
  over a `;` chain of attempts — instead of one throwaway
  `run_chr_session/1` fork per candidate signature. Verdicts are
  unchanged. One difference in kind: a runtime error inside an
  attempt now aborts the check and surfaces as that error, rather
  than reading as one more signature that did not fit.

VM program header: a new optional `inert-types` entry lists the
constraint types whose activation runs no occurrence procedure
(no occurrences, or only passive ones). A runtime may skip registering
such a constraint as an observer of the variables in its arguments;
honoring the entry changes no result, only the reactivation traffic.
The Haskell runtime honors it, the Scheme backend ignores it. A
program serialized before the entry existed still reads, declaring no
inert type. See the [VM specification](docs/reference/vm.md).

- This, together with an enqueue-time liveness filter on observers
  and a per-branch cursor in the search driver, makes a search path
  linear in its depth where it was quadratic: a path of ten thousand
  choice points went from about 15 s to under 0.2 s.
- `run_chr_session/1` is now the same driver: `solve/1` made total.
  Same fork, same commit on the first solution, with a runtime error
  in the goal reported as `false` instead of propagating — its one
  distinct job, and the language's only error catcher. Two changes in
  behaviour: a `false` result is now fully rolled back, where the
  sub-session's bindings used to be left in place, and a choice point
  the goal tells is explored instead of sitting inert. A misspelled or
  unexported goal constraint is still a loud caller error, not a
  `false`.

Soundness fix: `GuardEqual` evidence (the fact a shared head variable
contributes) no longer treats value equality as full type equality. A
value determines its type's outermost constructor nominally but not
the constructor's parameters (`[]` inhabits `list(T)` for every `T`),
so at a rigid type variable the evidence now pins a base type or
nullary constructor application exactly, pins a parametric application
or function type only at *fresh rigid* parameters (the `GuardMatch`
discipline), and derives nothing at the parameter positions of a
shared constructor — no pins, no merges, and no
inaccessible-branch warning. Whole-type rigid-to-rigid merges (the
multi-head transitivity idiom) are unchanged. Found by the
type-soundness property test; see
`docs/reference/type-system.md` §Guard-Derived Type Evidence.

- Programs that exploited the hole now fail to check (typically
  `YCHR-60001`): a fully-typed program could previously bind a `bool`
  into an `int`-declared position through a constraint polymorphic in
  a type parameter.
- Some `YCHR-20104` warnings no longer fire, because the rules they
  marked dead can in fact fire: a parameter-only mismatch between two
  positions sharing a variable (`box(int)` vs `box(bool)` — live via
  `empty`), and the self-referential equality `T` \~ `list(T)`, which
  now pins `T := list(B)` (live via `[]`) instead of warning.

Breaking: a data-constructor name may no longer pun on a function
name. Previously the two were told apart by syntactic position —
pattern positions took the constructor, evaluating positions took the
function — so the same text meant different things in different parts
of one rule, silently.

- Declaring a constructor and a function with the same name in one
  module is now `YCHR-16020` (`ConstructorFunctionCollision`). Both
  spell as `mod:name`, so qualifying could not disambiguate.
- A *bare* reference to a name visible as a constructor from one
  module and as a function from another is now `YCHR-20020`
  (`ConstructorFunctionAmbiguity`). Qualified references
  (`node:leaf(grow:leaf(N))`) keep working and are the intended fix.
- Arity is not part of either comparison: `foo/0` the constructor
  collides with `foo/1` the function.
- `fun name/arity` references and `quote(...)` contents are
  unaffected — neither is a place where the two namespaces compete,
  and neither is a constraint name: a constraint may still share a
  name with a data constructor.

Every module imports the prelude in full, so a constructor may not be
referred to bare under a name the prelude declares as a function.
Accordingly, the STLC example's object-language variable node is now
`evar/1` rather than `var/1`.

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

Rule guards now tolerate under-instantiation. A guard that cannot be
decided — because an unbound logical variable reached a point that
demanded its value — evaluates to false instead of aborting the query:
the rule does not fire, and when the variable is bound later, ordinary
constraint reactivation retries the occurrence. This is on for every
rule guard, with no new surface syntax. See
[§Soft guard failure](docs/reference/language.md#soft-guard-failure).

- The catch is at the rule-guard boundary and nowhere else. An `is`
  right-hand side, a rule body and a top-level goal still fail hard,
  and an instantiation failure inside a function's equation guard
  propagates out of the function rather than falling through to the
  next equation.
- Runtime errors now carry a kind internally, which is what tells the
  two apart. Failures diagnosed as insufficient instantiation are
  worded "… is not sufficiently instantiated (unbound variable)".
  The strict host primitives — `+ - * / div mod rem`, `< > =< >=`,
  `int_to_float`, `float_to_int`, the `string_*` operations, `write`,
  `writeln`, `compound_to_list`, `list_to_compound` — report that
  wording where an unbound argument previously produced a type-shaped
  message. Primitives total on unbound values (`==`, `unifiable`, the
  type predicates, `term_variables`, `copy_term`) are unaffected, and
  no call that succeeded before fails now.
- A host function whose argument marshalling reports `UnboundValue` is
  classified the same way, so a guard calling one delays too. Decoding
  the argument as `Term` opts out.
- A guard whose value is an unbound variable delays (the guard position
  demands a boolean); one that evaluates to a *bound* non-boolean is
  still the hard error "guard did not evaluate to a boolean".
- The boundness-guard idiom (`integer(N), N > 0 | …`) documented under
  [§No mode checking](docs/reference/type-system.md) is now a matter of
  style rather than a requirement — the unguarded rule gets the same
  schedule.
- New VM boolean form `bsoft-guard`; backends must implement it. Both
  backends do, and agree on every golden case: the Scheme runtime tags
  its strict primitives' failures the same way, and lowers `bfrom-val`
  through a boolean check rather than letting Scheme truthiness decide
  (an unbound variable is a record, hence truthy, and would have read
  as *true*).

Two Scheme-backend conformance fixes found while classifying the above,
both cases where the backend accepted what the Haskell runtime rejects:

- `list_to_compound` now rejects an improper tail and a non-atom head,
  not just an empty list. `list_to_compound([f, x | T])` quietly
  returned `f(x)`, and `list_to_compound([1, 2])` built a term whose
  functor was a number — which then escaped as a raw wrong-type
  condition from the pretty-printer rather than as a CHR error.
- `write` and `writeln` now require a string, as their prelude
  signatures already declare and as the Haskell runtime already
  enforced. Previously any bound value was displayed.

Stdlib additions, both implemented on both backends:

- `library(meta)` gains `name_base/1`, the local part of a name atom
  (`mod:foo` → `foo`, an unqualified name unchanged). Two names have
  the same base exactly when their unqualified spellings agree, which
  is how a program can recognize a name without knowing which module
  declared it. A non-atom argument is a runtime error; an *unbound*
  one is an instantiation failure, so a rule guard calling it delays
  rather than aborting. See [`libraries/meta.chr`](libraries/meta.chr).
- The ordering operators `<`, `>`, `=<` and `>=` gain a
  `(string, string) -> bool` signature alongside their `int` and
  `float` ones, so strings compare with the ordinary operators rather
  than a separate function. The order is lexicographic by code point:
  case-sensitive, following no locale's collation rules. There is
  still no mixed-type comparison — `1 < "a"` matches no signature
  (`YCHR-60006`). Because `max/2` and `min/2` are declared
  `requiring '>='(T, T) -> bool` / `'=<'(T, T) -> bool`, they now work
  on strings too; the prelude reference's claim that they were
  limited to the two numeric types is corrected accordingly. See
  [`libraries/prelude.chr`](libraries/prelude.chr).

Library API:

- `YCHR.Run` gains `resolveQueryGoals` and the `ResolvedQuery` record
  it returns: everything `prepareQuery` does — parse, rename, resolve,
  desugar, lambda-lift — short of type-checking, plus the program the
  resulting goals are to be checked against. `prepareQuery` is now
  defined in terms of it. Use it when you want the goals themselves,
  or want to type-check them yourself, rather than take
  `prepareQuery`'s all-or-nothing `TypeErrors`. Like the rest of the
  staged query pipeline it is outside the version policy.

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
