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
          get-var-id
          *wildcard*
          wildcard?)
  (import (rnrs)
          (ychr session))

  ;;; Wildcard sentinel
  (define *wildcard* (list 'wildcard))
  (define (wildcard? v) (eq? v *wildcard*))

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

  ;;; Unification (tell semantics, Prolog =)
  (define (unify v1 v2)
    (let ((observers '()))
      (define (emit! obs)
        (set! observers (append obs observers)))
      (let ((result (unify* (deref v1) (deref v2) emit!)))
        (values result observers))))

  (define (unify* d1 d2 emit!)
    (cond
      ((wildcard? d1) #t)
      ((wildcard? d2) #t)
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
  (define (unifiable? v1 v2)
    (let ((trail '()))
      (define (trail! v)
        ;; Record the current var-value so it can be restored later.
        (set! trail (cons (cons v (var-value v)) trail)))
      (define (uni a b)
        (uni* (deref a) (deref b)))
      (define (uni* d1 d2)
        (cond
          ((wildcard? d1) #t)
          ((wildcard? d2) #t)
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
      ((and (integer? d1) (integer? d2)) (eqv? d1 d2))
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
  (define (match-term v functor arity)
    (let ((d (deref v)))
      (and (term? d)
           (eq? (term-functor d) functor)
           (= (vector-length (term-args d)) arity))))

  (define (get-arg v idx)
    (vector-ref (term-args (deref v)) idx))

  ;;; Observer management
  (define (add-observer! suspension-id v)
    (let ((d (deref v)))
      (when (and (var? d) (eq? (var-value d) *unbound*))
        (var-observers-set! d (cons suspension-id (var-observers d))))))

  ;;; Var ID extraction
  (define (get-var-id v)
    (let ((d (deref v)))
      (if (and (var? d) (eq? (var-value d) *unbound*))
          (var-id d)
          #f)))
)
