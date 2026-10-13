;;;; CHR session record — bundles all mutable runtime state.
(library (ychr session)
  (export make-session
          %make-session-record
          session?
          make-counters
          %%make-counters
          counters?
          counters-var-id counters-var-id-set!
          counters-store-next-id counters-store-next-id-set!
          session-counters
          session-var-id session-var-id-set!
          session-store-by-type session-store-by-type-set!
          session-index-positions
          session-store-index session-store-index-set!
          session-type-names
          session-store-next-id session-store-next-id-set!
          session-history session-history-set!
          session-queue-front session-queue-front-set!
          session-queue-back session-queue-back-set!
          session-evaluables
          session-callables
          session-tellables
          session-op-table
          session-goals
          session-short-exports
          session-exported-goals
          session-inert
          session-alt-type
          session-owner)
  (import (rnrs))

  ;;; The identifiers a session hands out: logical-variable ids and
  ;;; suspension ids. One record, shared by every fork of a session, so
  ;;; a fork and its caller never hand out the same id. Both counters
  ;;; stay monotonic across backtracking, as in the Haskell runtime: an
  ;;; id burned in an abandoned branch is never handed out again, so a
  ;;; stale observer id can only ever miss, never collide.
  (define-record-type (counters %%make-counters counters?)
    (fields (mutable var-id counters-var-id counters-var-id-set!)
            (mutable store-next-id
                     counters-store-next-id
                     counters-store-next-id-set!)))

  ;; The constructor under the name the rest of the runtime and the
  ;; tests use. An alias rather than a rename: R6RS has no binding-renaming
  ;; export without the `rename` sub-form, and this keeps the record's own
  ;; names untouched.
  (define (make-counters var-id store-next-id)
    (%%make-counters var-id store-next-id))

  ;; The session record's constructor, under the name every caller and the
  ;; generated library use.
  (define (make-session counters
                        store-by-type
                        index-positions
                        store-index
                        type-names
                        history
                        queue-front
                        queue-back
                        evaluables
                        callables
                        tellables
                        op-table
                        goals
                        short-exports
                        exported-goals
                        inert
                        alt-type
                        owner)
    (%make-session-record counters
                          store-by-type
                          index-positions
                          store-index
                          type-names
                          history
                          queue-front
                          queue-back
                          evaluables
                          callables
                          tellables
                          op-table
                          goals
                          short-exports
                          exported-goals
                          inert
                          alt-type
                          owner))

  ;; `evaluables` holds the deep-eval dispatch table for the @is@
  ;; operator (functor + arity → procedure). `callables` holds the
  ;; closure-apply dispatch table for `$call` (closure functor +
  ;; identity + arity → procedure). `tellables` holds the dynamic
  ;; `tell/N` dispatch table (calling module + goal functor + arity →
  ;; tell procedure). All three are populated once at library load
  ;; time, via `register-evaluable!`, `register-callable!` and
  ;; `register-tellable!` respectively, and never mutated after; hence
  ;; immutable in the record.
  ;;
  ;; `index-positions` is the per-type set of argument positions the
  ;; program looks up through a `Foreach` index condition — a vector of
  ;; position lists, built once by `%make-session` from what the
  ;; compiler emitted, and immutable after. `store-index` is the
  ;; per-argument store index those positions are answered from (see
  ;; `store.sls`): a vector indexed by constraint type whose entries
  ;; start out `#f` and become an index once the type's bucket crosses
  ;; `index-threshold`. The field is mutable because a search branch may
  ;; index a type and the driver restores the whole pointer when it
  ;; unwinds — a fork shares the caller's vector, so putting the `#f`
  ;; back has to be able to replace it. A vector cell written while a
  ;; type stayed unindexed needs no undo: appending a suspension to an
  ;; unindexed type files nothing, and restoring the growable's count
  ;; truncates it.
  ;;
  ;; `type-names` is the source name of each constraint type, indexed by
  ;; the same constraint-type integer the store uses: the compiler's
  ;; `vmName` mangling of `CompiledProgram.typeNames`, emitted by the
  ;; generated library as `%make-session`'s fourth argument (see
  ;; `Scheme.hs`'s `typeNamesSExpr`). `write_store_to_list` and
  ;; `print_store` split each entry at the first `__` to recover the
  ;; module and base the reference's `constraintAsValue` needs; a
  ;; hand-built session that passes no names — or an index past the
  ;; vector — falls back to the `c#type_N` label. Immutable.
  ;;
  ;; `op-table` is the operator table `read_term_from_string` parses
  ;; with: the program's own table, built by the generated library and
  ;; handed to `%make-session` (see `(ychr optable)`), or
  ;; `builtin-op-table` for a hand-built session — the same
  ;; `builtinOps` default `initSessionEnv` gives one. Immutable.
  ;;
  ;; `goals`, `short-exports`, `inert` and `alt-type` are the search
  ;; driver's program-level tables, populated by the generated library's
  ;; `register-goal!` / `register-short-export!` and by `%make-session`:
  ;;
  ;;   * `goals`: `(functor . arity)` — the functor a compiled term
  ;;     carries — → `(tell-procedure . exported?)`. The driver resolves
  ;;     a goal's name to a qualified functor and looks the tell
  ;;     procedure up here; it is this backend's counterpart of the
  ;;     Haskell runtime's `procMap` lookup.
  ;;   * `short-exports`: `(name . arity)` (an *unqualified* surface
  ;;     name) → the resolved mangled functor symbol when exactly one
  ;;     module exports it, or a list of module names when several do.
  ;;     The driver's `resolveByExport`.
  ;;   * `inert`: one boolean per constraint type, `#t` for a type the
  ;;     compiler marked inert (`YCHR.Internal.VM.Program.inertTypes`).
  ;;     A suspension of one of those types is not registered as an
  ;;     observer of the variables in its arguments, because
  ;;     reactivating it could do nothing.
  ;;   * `alt-type`: the constraint type index whose name is
  ;;     `search:alt`, or `#f` when the program never declares it. The
  ;;     driver's choice points live in that type's bucket.
  ;;
  ;; `owner` is the identity token of the store this session's
  ;; constraints belong to: the `store-by-type` object itself for a
  ;; session built from scratch, and the caller's token for a `'copy`
  ;; fork (whose `store-by-type` *is* the caller's object). The driver
  ;; drops a reactivation enqueued for a suspension of another session's
  ;; store.
  (define-record-type (session %make-session-record session?)
    (fields (immutable counters session-counters)
            (mutable store-by-type session-store-by-type session-store-by-type-set!)
            (immutable index-positions session-index-positions)
            (mutable store-index session-store-index session-store-index-set!)
            (immutable type-names session-type-names)
            (mutable history session-history session-history-set!)
            (mutable queue-front session-queue-front session-queue-front-set!)
            (mutable queue-back session-queue-back session-queue-back-set!)
            (immutable evaluables session-evaluables)
            (immutable callables session-callables)
            (immutable tellables session-tellables)
            (immutable op-table session-op-table)
            (immutable goals session-goals)
            (immutable short-exports session-short-exports)
            (immutable exported-goals session-exported-goals)
            (immutable inert session-inert)
            (immutable alt-type session-alt-type)
            (immutable owner session-owner)))

  ;; The two accessors the rest of the runtime had before the counters
  ;; moved into a shared record. A fork shares the caller's counters, so
  ;; these read and write through that one object.
  (define (session-var-id s) (counters-var-id (session-counters s)))
  (define (session-var-id-set! s n)
    (counters-var-id-set! (session-counters s) n))
  (define (session-store-next-id s) (counters-store-next-id (session-counters s)))
  (define (session-store-next-id-set! s n)
    (counters-store-next-id-set! (session-counters s) n))
)
