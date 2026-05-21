;;;; Umbrella library: re-exports the user-facing surface of the YCHR
;;;; Scheme runtime, pretty-printer, and interactive helpers. Users
;;;; can write a single import:
;;;;
;;;;   (import (ychr) (ychr generated <program>))
;;;;
;;;; instead of pulling in each component library individually.
;;;;
;;;; KEEP IN SYNC: R6RS has no re-export shorthand, so adding a new
;;;; public export to (ychr runtime), (ychr pretty), or (ychr repl)
;;;; means hand-extending the list below. The grouping comments mark
;;;; the sub-library each name comes from.
(library (ychr)
  (export
    ;; --- (ychr repl) -------------------------------------------------
    open-session tell
    ;; --- (ychr pretty) -----------------------------------------------
    pretty-term pretty-bindings bindings->string
    ;; --- (ychr runtime): vars, terms, unification --------------------
    make-var var? var-id deref unify unifiable? equal?/chr
    make-term term? term-functor term-args
    match-term get-arg
    ;; --- (ychr runtime): constraint store ----------------------------
    alive-constraint? constraint-id constraint-arg constraint-type
    id-equal? is-constraint-type? kill-constraint
    ;; --- (ychr runtime): helpers used in goals/scripting -------------
    %unify %unifiable? %nonvar? %ground? %print
    %term-variables %compound-to-list %list-to-compound %copy-term
    %nil %cons
    %int-to-float %float-to-int %idiv %imod %irem)
  (import (ychr runtime) (ychr pretty) (ychr repl))
)
