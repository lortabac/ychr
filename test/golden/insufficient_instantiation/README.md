# insufficient_instantiation

Pins the diagnostic distinction between the two ways function dispatch
can fail to select an equation:

- **Insufficient instantiation** — a structural pattern test was reached
  with an unbound logical variable at the position it inspects, so no
  verdict is possible; a later binding could still make an equation
  match.
- **Definite mismatch** — every equation was ruled out on values that
  are already instantiated.

Both are hard `YCHR-60001` runtime errors; only the message differs.

| case | reports | why |
|------|---------|-----|
| `mylen_partial_tail`, `mylen_unbound`, `mylen_wildcard_tail` | insufficient | functor and nil tests on a partial list, a free variable, and a tail spelled `_` (an anonymous variable, so also free) |
| `bit_unbound` | insufficient | HNF lowers a literal pattern to an equality test |
| `same_unbound` | insufficient, argument 2 | HNF's non-linear-pattern equality test, which has two scrutinees |
| `nest_inherited_index` | insufficient, argument 2 | the blocking test is on a value *extracted from* argument 2, so the reported index is inherited through the `pair` decomposition |
| `over_approximation` | insufficient, argument 1 | dispatch stops at the first failing test; argument 2 would have mismatched definitely, but that test is never reached |
| `bit_mismatch` | definite | every equation ruled out on an instantiated value |
| `pos_guard_failure` | definite | a *user-written* guard is a decision about values already in hand, so failing it is not inconclusive |
| `shadow_local_name` | definite | regression: a pattern variable named after a compiler-generated dispatch local must not clobber it (see below) |
| `len_of` | *positive* | makes the Scheme harness run this directory — it only collects `.goal`/`.expected` pairs |

`shadow_local_name` guards a real bug: a pattern variable compiles to a
local under its own source name, and the Haskell interpreter's
environment is flat per invocation, so a generated local that a source
variable can spell is one a source variable can clobber. The lexer's
`__` ban covers atoms only (`__Foo` is an ordinary variable), which is
why the dispatch locals are named with `$` — see `inconclusiveName` in
`src/YCHR/Internal/Compile/Names.hs`.

The `'$call'` counterpart is `test/golden/closure_dispatch_errors`.
