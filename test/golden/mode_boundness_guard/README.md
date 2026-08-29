# mode_boundness_guard

Pins the interaction between the limitation documented in
[§No mode checking](../../../docs/reference/type-system.md) of the type-system
reference and
[§Soft guard failure](../../../docs/reference/language.md) of the language
reference: YCHR types terms but does not track their *mode*, so a fully typed,
cleanly type-checking program can still reach an operation that demands a value
with a free variable. In a rule guard that is not fatal — the guard soft-fails
and the occurrence is retried after the variable is bound.

Both halves are fully typed and identical apart from one guard conjunct.
`cg`/`cu` is stored while its argument is unbound; `bind_g`/`bind_u` binds it
afterwards; `fire_g`/`fire_u` compares it.

- `guarded` — `integer(N)` fails on a free variable, so the rule is skipped at
  the first activation. Binding `E` reactivates the constraint and the rule
  fires on the later activation. Result `R = 1`.
- `unguarded` — the same rules without that conjunct reach `N > 0` while `N` is
  still free. The comparison raises an instantiation failure, the rule guard
  catches it as `false`, and the occurrence is retried after `E` is bound.
  Same result, `R = 1`.

The pair is what makes the point twice over. Statically, `integer(N)` at
`N : int` is redundant — the declaration already gives the type, and as an
evidence form it contributes a fact already known — so the two programs
type-check identically; that is the mark of an axis the type system does not
cover. Dynamically, they now also *behave* identically, because the guard
boundary tolerates the under-instantiation the type system cannot rule out.
The explicit `integer(N)` conjunct is a matter of style, not correctness.

The tell-time face of the same limitation is
`test/golden/evaluated_tell_args_unbound`, where there is no guard boundary to
catch the failure and it stays fatal; this directory covers the
store-and-reactivate face.
