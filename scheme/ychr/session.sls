;;;; CHR session record — bundles all mutable runtime state.
(library (ychr session)
  (export make-session session?
          session-var-id session-var-id-set!
          session-store-by-type session-store-by-type-set!
          session-index-positions
          session-store-index
          session-store-next-id session-store-next-id-set!
          session-history session-history-set!
          session-queue-front session-queue-front-set!
          session-queue-back session-queue-back-set!
          session-evaluables
          session-callables
          session-op-table)
  (import (rnrs))

  ;; `evaluables` holds the deep-eval dispatch table for the @is@
  ;; operator (functor + arity → procedure). `callables` holds the
  ;; closure-apply dispatch table for `$call` (closure functor +
  ;; identity + arity → procedure). Both are populated once at library
  ;; load time, via `register-evaluable!` and `register-callable!`
  ;; respectively, and never mutated after; hence immutable in the
  ;; record.
  ;;
  ;; `index-positions` is the per-type set of argument positions the
  ;; program looks up through a `Foreach` index condition — a vector of
  ;; position lists, built once by `%make-session` from what the
  ;; compiler emitted, and immutable after. `store-index` is the
  ;; per-argument store index those positions are answered from (see
  ;; `store.sls`): a vector indexed by constraint type whose entries
  ;; start out `#f` and become an index once the type's bucket crosses
  ;; `index-threshold`. The field is immutable, but the vector (and the
  ;; index structures it holds) is mutated in place — the Scheme runtime
  ;; has no snapshot or undo, so the index is simply session state.
  ;;
  ;; `op-table` is the operator table `read_term_from_string` parses
  ;; with: the program's own table, built by the generated library and
  ;; handed to `%make-session` (see `(ychr optable)`), or
  ;; `builtin-op-table` for a hand-built session — the same
  ;; `builtinOps` default `initSessionEnv` gives one. Immutable.
  (define-record-type (session make-session session?)
    (fields (mutable var-id session-var-id session-var-id-set!)
            (mutable store-by-type session-store-by-type session-store-by-type-set!)
            (immutable index-positions session-index-positions)
            (immutable store-index session-store-index)
            (mutable store-next-id session-store-next-id session-store-next-id-set!)
            (mutable history session-history session-history-set!)
            (mutable queue-front session-queue-front session-queue-front-set!)
            (mutable queue-back session-queue-back session-queue-back-set!)
            (immutable evaluables session-evaluables)
            (immutable callables session-callables)
            (immutable op-table session-op-table)))
)
