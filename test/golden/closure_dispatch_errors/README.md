# closure_dispatch_errors

The `'$call'` counterpart of `test/golden/insufficient_instantiation`.
Closure dispatch fails in the same ways function-equation dispatch does,
and must report them differently:

- `unbound_closure` — the closure operand is still an unbound logical
  variable, so no dispatch decision is possible.
- `not_a_closure` — the operand is an instantiated value that is not a
  function reference or a lifted lambda closure. This case is also the
  regression for the runtime's `__chr_error` reporter, which used to
  ignore its message argument and print "no matching equation" for
  every closure-dispatch failure.
- `funref_arity_mismatch` / `lambda_arity_mismatch` — the operand *is* a
  callable, but applied at an arity other than the one it was declared
  at. The program defines `scale/1` and `scale/2` so that the first case
  is a real cross-check: a dispatch key of (functor, identity) alone
  would silently reach `scale/2` and the goal would succeed instead of
  failing.
- `apply_ok` / `scale_ok` — successful `'$call'`s, which are what make
  the Scheme harness run this directory: it only collects
  `.goal`/`.expected` pairs.
- `driver_funref` — a goal whose argument *is* a function call carrying
  a function reference (`apply1(fun double/1, 5)`). The Scheme driver
  evaluates that argument itself, so this is the case that pins the
  driver's function-reference encoding: it must be the flattened
  `module:name` identity the callables table is keyed on, not the
  `module__name` mangling. `go/1` prints nothing, hence the empty
  `.expected`.
