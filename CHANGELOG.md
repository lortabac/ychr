# Revision history for ychr

## Unreleased

* **Breaking:** tell-side constraint arguments — in rule bodies and
  top-level goals — are now evaluated expressions, like every other
  expression position in the language. `foo(1 + 2)` evaluates `1 + 2`
  to `3` before the tell; `foo(plus(2, 3))` calls the `plus/2`
  function. The opt-out for passing a symbolic data term is the
  existing `term(...)` quoting form. Heads and equation patterns are
  unchanged (they still match on data shapes). An argument expression
  that mentions an unbound logical variable runtime-errors at tell
  time. See `docs/reference/language.md#constraint-arguments-evaluate`.

* `runProgramWithGoal{,DSL}` and `runPreparedGoal` now return just
  the per-query variable bindings (`Map Text Term`); the previously
  returned tell-procedure `Value` was always discarded by callers.

* The single-goal parser now picks up the program's user-declared
  operators (matching the multi-goal parser), so operators like `+`
  work in goal-argument position from the CLI.

* The Scheme library now exports `func_*` procedures in addition to
  `tell_*`, so generated drivers can call user-defined functions
  appearing in goal arguments.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
