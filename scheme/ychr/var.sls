;;;; Logical variables, compound terms, unification, and equality.
(library (ychr var)
  (export make-var
          var?
          var-id
          deref
          unify
          unifiable?
          equal?/chr
          make-term
          term?
          term-functor
          term-args
          match-term
          get-arg
          add-observer!
          add-observer-and-key
          ground-key
          get-var-id)
  (import (rnrs)
          (ychr session))

  ;;; Logical variables
  (define *unbound* (list 'unbound))

  (define-record-type (var %make-var var?)
    (fields (immutable id var-id)
            (mutable value var-value var-value-set!)
            (mutable observers var-observers var-observers-set!)))

  (define (make-var s)
    (let ((id (session-var-id s)))
      (session-var-id-set! s (+ id 1))
      (%make-var id *unbound* '())))

  ;;; Compound terms
  (define-record-type (term make-term term?)
    (fields (immutable functor term-functor)
            (immutable args term-args)))

  ;;; Dereferencing with path compression
  (define (deref v)
    (if (var? v)
        (let ((val (var-value v)))
          (if (eq? val *unbound*)
              v
              (let ((result (deref val)))
                (when (not (eq? result v))
                  (var-value-set! v result))
                result)))
        v))

  ;;; Dereferencing without path compression.
  ;;;
  ;;; Only unifiable? uses this, and it must. That check's own writes
  ;;; are hypothetical and rolled back from a private trail, but a
  ;;; compression write made *through* one of them touches a different
  ;;; cell, is not on that trail, and would survive the rollback --
  ;;; leaving a variable bound to a value the check merely supposed.
  ;;; For W aliased to V: the check tentatively binds V to 1, then
  ;;; dereferences W, walks W -> V -> 1, and compresses W to 1.
  ;;; Restoring V then leaves W bound to 1 and the alias destroyed,
  ;;; whatever the check answered.
  (define (deref/no-compress v)
    (if (var? v)
        (let ((val (var-value v)))
          (if (eq? val *unbound*)
              v
              (deref/no-compress val)))
        v))

  ;;; Unification (tell semantics, Prolog =)
  (define (unify v1 v2)
    (let ((observers '()))
      (define (emit! obs)
        (set! observers (append obs observers)))
      (let ((result (unify* (deref v1) (deref v2) emit!)))
        (values result observers))))

  (define (unify* d1 d2 emit!)
    (cond
      ((and (var? d1) (var? d2) (eq? d1 d2)) #t)
      ((and (var? d1) (var? d2))
       (let ((obs1 (var-observers d1))
             (obs2 (var-observers d2)))
         (var-value-set! d1 d2)
         (var-observers-set! d1 '())
         (var-observers-set! d2 (append obs1 obs2))
         (emit! obs1)
         #t))
      ((var? d1)
       (let ((obs (var-observers d1)))
         (var-value-set! d1 d2)
         (var-observers-set! d1 '())
         (emit! obs)
         #t))
      ((var? d2)
       (unify* d2 d1 emit!))
      ((and (integer? d1) (integer? d2))
       (eqv? d1 d2))
      ((and (symbol? d1) (symbol? d2))
       (eq? d1 d2))
      ((and (boolean? d1) (boolean? d2))
       (eq? d1 d2))
      ((and (string? d1) (string? d2))
       (string=? d1 d2))
      ((and (term? d1) (term? d2)
            (eq? (term-functor d1) (term-functor d2))
            (= (vector-length (term-args d1))
               (vector-length (term-args d2))))
       (unify-args (term-args d1) (term-args d2) 0 emit!))
      (else #f)))

  (define (unify-args v1 v2 i emit!)
    (if (>= i (vector-length v1))
        #t
        (let-values (((ok obs) (unify (vector-ref v1 i) (vector-ref v2 i))))
          (emit! obs)
          (if ok
              (unify-args v1 v2 (+ i 1) emit!)
              #f))))

  ;;; Unifiability check: does unify succeed, without mutating any
  ;;; bindings? Mirrors unify*/unify-args but uses a trail list to roll
  ;;; back every mutation before returning. Observers are never touched.
  ;;;
  ;;; The walk uses deref/no-compress rather than deref, so that the
  ;;; trail is the only writer; see there.
  (define (unifiable? v1 v2)
    (let ((trail '()))
      (define (trail! v)
        ;; Record the current var-value so it can be restored later.
        (set! trail (cons (cons v (var-value v)) trail)))
      (define (uni a b)
        (uni* (deref/no-compress a) (deref/no-compress b)))
      (define (uni* d1 d2)
        (cond
          ((and (var? d1) (var? d2) (eq? d1 d2)) #t)
          ((var? d1)
           (trail! d1)
           (var-value-set! d1 d2)
           #t)
          ((var? d2)
           (trail! d2)
           (var-value-set! d2 d1)
           #t)
          ((and (integer? d1) (integer? d2)) (eqv? d1 d2))
          ((and (symbol? d1) (symbol? d2)) (eq? d1 d2))
          ((and (boolean? d1) (boolean? d2)) (eq? d1 d2))
          ((and (string? d1) (string? d2)) (string=? d1 d2))
          ((and (term? d1) (term? d2)
                (eq? (term-functor d1) (term-functor d2))
                (= (vector-length (term-args d1))
                   (vector-length (term-args d2))))
           (uni-args (term-args d1) (term-args d2) 0))
          (else #f)))
      (define (uni-args v1 v2 i)
        (if (>= i (vector-length v1))
            #t
            (if (uni (vector-ref v1 i) (vector-ref v2 i))
                (uni-args v1 v2 (+ i 1))
                #f)))
      (let ((result (uni v1 v2)))
        ;; Restore every trailed var to its original value. Entries are
        ;; prepended newest-first, so walking front-to-back restores each
        ;; cell to its oldest captured state.
        (for-each (lambda (entry)
                    (var-value-set! (car entry) (cdr entry)))
                  trail)
        result)))

  ;;; Equality (ask semantics, Prolog ==)
  (define (equal?/chr v1 v2)
    (equal* (deref v1) (deref v2)))

  (define (equal* d1 d2)
    (cond
      ((and (var? d1) (var? d2)) (eq? d1 d2))
      ((or (var? d1) (var? d2)) #f)
      ;; Numeric equality. eqv? distinguishes exact and inexact, so an
      ;; integer is never equal to a flonum even when their values
      ;; coincide — matching the Haskell side which keeps VInt and
      ;; VFloat separate.
      ((and (number? d1) (number? d2)) (eqv? d1 d2))
      ((and (symbol? d1) (symbol? d2)) (eq? d1 d2))
      ((and (boolean? d1) (boolean? d2)) (eq? d1 d2))
      ((and (string? d1) (string? d2)) (string=? d1 d2))
      ((and (term? d1) (term? d2)
            (eq? (term-functor d1) (term-functor d2))
            (= (vector-length (term-args d1))
               (vector-length (term-args d2))))
       (equal-args (term-args d1) (term-args d2) 0))
      (else #f)))

  (define (equal-args v1 v2 i)
    (if (>= i (vector-length v1))
        #t
        (if (equal?/chr (vector-ref v1 i) (vector-ref v2 i))
            (equal-args v1 v2 (+ i 1))
            #f)))

  ;;; Term operations
  ;; 0-arity compounds collapse to symbols at the runtime layer
  ;; (matching the Haskell side's VAtom canonical form), so a symbol
  ;; matches when arity is 0 and its name equals functor.
  (define (match-term v functor arity)
    (let ((d (deref v)))
      (cond
        ((symbol? d) (and (= arity 0) (eq? d functor)))
        ((term? d)
         (and (eq? (term-functor d) functor)
              (= (vector-length (term-args d)) arity)))
        (else #f))))

  (define (get-arg v idx)
    (vector-ref (term-args (deref v)) idx))

  ;;; Observer management
  ;; Register an observer on every unbound variable reachable from a
  ;; value: a bare unbound variable directly, and every variable nested
  ;; inside a compound term's arguments (e.g. the X in pair(X, 1) or
  ;; [X, X]) by recursion. Without the recursion a constraint stored
  ;; with such an argument would never be reactivated when the nested
  ;; variable is later bound, missing an omega-r Reactivate step.
  (define (add-observer! suspension-id v)
    (let ((d (deref v)))
      (cond
        ((and (var? d) (eq? (var-value d) *unbound*))
         (var-observers-set! d (cons suspension-id (var-observers d))))
        ((term? d)
         (add-observer-args! suspension-id (term-args d) 0)))))

  (define (add-observer-args! suspension-id args i)
    (when (< i (vector-length args))
      (add-observer! suspension-id (vector-ref args i))
      (add-observer-args! suspension-id args (+ i 1))))

  ;;; Ground keys
  ;;;
  ;;; The key of a constraint argument, for the store's per-argument
  ;;; indexes (the paper's Indexing optimization; see store.sls). It
  ;;; mirrors `groundKey`/`addObserverAndKey` in
  ;;; src/YCHR/Internal/Runtime/Var.hs.
  ;;;
  ;;; A key is ordinary Scheme data, compared with `equal?` (which uses
  ;;; `eqv?` on numbers, so an exact 1 and an inexact 1.0 stay
  ;;; distinct, exactly as `equal?/chr` keeps them):
  ;;;
  ;;;   (num . n)       a number, with `number-key` normalization below
  ;;;   (atom . s)      a symbol
  ;;;   (text . s)      a string
  ;;;   (bool . b)      a boolean
  ;;;   (term f k ...)  a compound: functor plus one key per argument
  ;;;
  ;;; `#f` means "not ground": an unbound variable, a compound holding
  ;;; one, or any value `equal?/chr` never equates with anything. Such
  ;;; an argument goes to its position's non-ground fallback set, which
  ;;; every lookup for that position scans, so the index may only ever
  ;;; narrow a lookup to a superset of the matches. Key equality is
  ;;; deliberately never finer than `equal?/chr`: `number-key` collapses
  ;;; 0.0 and -0.0 (which `eqv?` distinguishes) and every NaN, which
  ;;; only ever yields extra candidates for the per-candidate check to
  ;;; reject.
  (define (ground-key v) (value-key v #f))

  ;;; One traversal with the two jobs an indexed constraint argument
  ;;; needs: register `suspension-id` as an observer on every unbound
  ;;; variable reachable from `v` — exactly what `add-observer!` does —
  ;;; and return `v`'s ground key. They share a traversal because they
  ;;; inspect the same term the same way; a store that indexes a
  ;;; position would otherwise walk each of its arguments twice.
  ;;;
  ;;; Meeting an unbound variable does not stop the walk — the variables
  ;;; behind it still need observing — it only discards the key, so the
  ;;; whole argument is always visited. An observer id of `#f` (never a
  ;;; valid suspension) means "compute the key only", which is what
  ;;; `ground-key` and the store's on-demand backlog pass need.
  (define (add-observer-and-key suspension-id v)
    (value-key v suspension-id))

  ;;; The normalized key payload of a number. The `flonum?` guard is what
  ;;; makes the test total: `nan?` raises on a non-real complex, which
  ;;; `equal?/chr` would have compared with `eqv?` quite happily, so an
  ;;; unguarded test could make a store that used to work raise once its
  ;;; type crossed the index threshold. `zero?` is total on every number,
  ;;; and an exact non-integer (a rational, which only a
  ;;; wider-than-Haskell host call can produce) passes through and keeps
  ;;; `eqv?`'s exact/inexact distinction because `equal?` on numbers is
  ;;; `eqv?`.
  (define (number-key x)
    (cond ((and (flonum? x) (nan? x)) 'nan)
          ((zero? x) 0)
          (else x)))

  (define (value-key v oid)
    (let ((d (deref v)))
      (cond
        ((and (var? d) (eq? (var-value d) *unbound*))
         (when oid
           (var-observers-set! d (cons oid (var-observers d))))
         #f)
        ((number? d) (cons 'num (number-key d)))
        ((symbol? d) (cons 'atom d))
        ((string? d) (cons 'text d))
        ((boolean? d) (cons 'bool d))
        ((term? d)
         (let* ((args (term-args d))
                (n (vector-length args)))
           (let loop ((i 0) (keys '()) (ground? #t))
             (if (= i n)
                 (and ground?
                      (cons 'term (cons (term-functor d) (reverse keys))))
                 (let ((k (value-key (vector-ref args i) oid)))
                   (loop (+ i 1) (cons k keys) (and ground? (if k #t #f))))))))
        (else #f))))

  ;;; Var ID extraction
  (define (get-var-id v)
    (let ((d (deref v)))
      (if (and (var? d) (eq? (var-value d) *unbound*))
          (var-id d)
          #f)))
)
