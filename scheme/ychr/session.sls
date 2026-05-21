;;;; CHR session record — bundles all mutable runtime state.
(library (ychr session)
  (export make-session session?
          session-var-id session-var-id-set!
          session-store-by-type session-store-by-type-set!
          session-store-next-id session-store-next-id-set!
          session-history session-history-set!
          session-queue-front session-queue-front-set!
          session-queue-back session-queue-back-set!
          session-evaluables)
  (import (rnrs))

  ;; `evaluables` holds the deep-eval dispatch table for the @is@
  ;; operator (functor + arity → procedure). It is populated once at
  ;; library load time via `register-evaluable!` and never mutated
  ;; after; hence immutable in the record.
  (define-record-type (session make-session session?)
    (fields (mutable var-id session-var-id session-var-id-set!)
            (mutable store-by-type session-store-by-type session-store-by-type-set!)
            (mutable store-next-id session-store-next-id session-store-next-id-set!)
            (mutable history session-history session-history-set!)
            (mutable queue-front session-queue-front session-queue-front-set!)
            (mutable queue-back session-queue-back session-queue-back-set!)
            (immutable evaluables session-evaluables)))
)
