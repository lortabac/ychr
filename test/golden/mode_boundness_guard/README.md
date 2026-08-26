# mode_boundness_guard

Pins the limitation documented in
[§No mode checking](../../../docs/reference/type-system.md) of the type-system
reference: YCHR types terms but does not track their *mode*, so a fully typed,
cleanly type-checking program can still reach an operation that demands a
value with a free variable.

Both halves are fully typed and identical apart from one guard conjunct.
`cg`/`cu` is stored while its argument is unbound; `bind_g`/`bind_u` binds it
afterwards; `fire_g`/`fire_u` compares it.

- `guarded` — `integer(N)` fails on a free variable, so the rule is skipped at
  the first activation. Binding `E` reactivates the constraint and the rule
  fires on the later activation. Result `R = 1`.
- `unguarded` — the same rules without that conjunct reach `N > 0` while `N`
  is still free, raising `YCHR-60001` from `prelude:'>'/2`.

The pair is what makes the point: `integer(N)` at `N : int` is *statically*
redundant — the declaration already gives the type, and as an evidence form it
contributes a fact already known — so the two programs type-check identically.
Only their execution differs, which is the mark of an axis the type system
does not cover.

The tell-time face of the same limitation is
`test/golden/evaluated_tell_args_unbound`; this directory covers the
store-and-reactivate face.
