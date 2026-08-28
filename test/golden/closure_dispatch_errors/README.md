# closure_dispatch_errors

The `'$call'` counterpart of `test/golden/insufficient_instantiation`.
Closure dispatch fails in the same two ways function-equation dispatch
does, and must report them differently:

- `unbound_closure` — the closure operand is still an unbound logical
  variable, so none of the dispatch branches can decide anything.
- `not_a_closure` — the operand is an instantiated value that is not a
  function reference or a lifted lambda closure. This case is also the
  regression for the runtime's `__chr_error` reporter, which used to
  ignore its message argument and print "no matching equation" for
  every closure-dispatch failure.
- `apply_ok` — a successful `'$call'`, which is what makes the Scheme
  harness run this directory: it only collects `.goal`/`.expected`
  pairs.
