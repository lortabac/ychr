;;;; Logical variables, compound terms, unification, and equality.
;;;;
;;;; This module provides the foundational layer of the CHR Scheme runtime:
;;;; mutable logical variables with binding chains, Prolog-style unification
;;;; (tell semantics) and equality checking (ask semantics), and compound
;;;; term construction and inspection.
;;;;
;;;; Unification collects observer IDs from bound variables, enabling
;;;; selective constraint reactivation.  Path compression is applied
;;;; during dereferencing to amortize future lookups.

;;; --------------------------------------------------------------------------
;;; Wildcard sentinel
;;; --------------------------------------------------------------------------

(define *wildcard* (list 'wildcard))

(define (wildcard? v) (eq? v *wildcard*))

;;; --------------------------------------------------------------------------
;;; Logical variables
;;; --------------------------------------------------------------------------

;; A logical variable is a mutable record.  When unbound, the value slot
;; holds the *unbound* sentinel and the observers slot holds a list of
;; suspension IDs (fixnums) that watch this variable.  When bound, the
;; value slot holds the bound value (which may be another variable,
;; forming a binding chain).

(define *unbound* (list 'unbound))

(define-record-type <var>
  (%make-var id value observers)
  var?
  (id var-id)
  (value var-value var-value-set!)
  (observers var-observers var-observers-set!))

(define *next-var-id* 0)

(define (make-var)
  (let ((id *next-var-id*))
    (set! *next-var-id* (+ id 1))
    (%make-var id *unbound* '())))

(define (reset-var-counter!)
  (set! *next-var-id* 0))

;;; --------------------------------------------------------------------------
;;; Compound terms
;;; --------------------------------------------------------------------------

;; A compound term has a symbol functor and a vector of arguments.
;; The vector gives O(1) access for get-arg.

(define-record-type <term>
  (make-term functor args)
  term?
  (functor term-functor)
  (args term-args))

;;; --------------------------------------------------------------------------
;;; Dereferencing with path compression
;;; --------------------------------------------------------------------------

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

;;; --------------------------------------------------------------------------
;;; Unification (tell semantics, Prolog =)
;;; --------------------------------------------------------------------------

;; Returns (values success? observer-list).
;; observer-list contains the suspension IDs that were watching any
;; variable that got bound during this unification.

(define (unify v1 v2)
  (let ((observers '()))
    (define (emit! obs)
      (set! observers (append obs observers)))
    (let ((result (unify* (deref v1) (deref v2) emit!)))
      (values result observers))))

;; Both arguments must already be dereferenced.
(define (unify* d1 d2 emit!)
  (cond
    ;; Wildcard
    ((wildcard? d1) #t)
    ((wildcard? d2) #t)
    ;; Var-Var, same variable
    ((and (var? d1) (var? d2) (eq? d1 d2))
     #t)
    ;; Var-Var, different variables: bind first to second, merge observers
    ((and (var? d1) (var? d2))
     (let ((obs1 (var-observers d1))
           (obs2 (var-observers d2)))
       (var-value-set! d1 d2)
       (var-observers-set! d1 '())
       (var-observers-set! d2 (append obs1 obs2))
       (emit! obs1)
       #t))
    ;; Var-NonVar: bind var to value
    ((var? d1)
     (let ((obs (var-observers d1)))
       (var-value-set! d1 d2)
       (var-observers-set! d1 '())
       (emit! obs)
       #t))
    ;; NonVar-Var: symmetric
    ((var? d2)
     (unify* d2 d1 emit!))
    ;; Integer-Integer
    ((and (integer? d1) (integer? d2))
     (eqv? d1 d2))
    ;; Symbol-Symbol (atoms)
    ((and (symbol? d1) (symbol? d2))
     (eq? d1 d2))
    ;; Boolean-Boolean
    ((and (boolean? d1) (boolean? d2))
     (eq? d1 d2))
    ;; String-String (text)
    ((and (string? d1) (string? d2))
     (string=? d1 d2))
    ;; Term-Term: same functor and arity, pairwise unify args
    ((and (term? d1) (term? d2)
          (eq? (term-functor d1) (term-functor d2))
          (= (vector-length (term-args d1))
             (vector-length (term-args d2))))
     (unify-args (term-args d1) (term-args d2) 0 emit!))
    ;; Everything else fails
    (else #f)))

(define (unify-args v1 v2 i emit!)
  (if (>= i (vector-length v1))
      #t
      (let-values (((ok obs) (unify (vector-ref v1 i) (vector-ref v2 i))))
        (emit! obs)
        (if ok
            (unify-args v1 v2 (+ i 1) emit!)
            #f))))

;;; --------------------------------------------------------------------------
;;; Equality (ask semantics, Prolog ==)
;;; --------------------------------------------------------------------------

;; No mutation beyond path compression during dereferencing.
;; Two distinct unbound variables are NOT equal.

(define (equal?/chr v1 v2)
  (equal*  (deref v1) (deref v2)))

;; Both arguments must already be dereferenced.
(define (equal* d1 d2)
  (cond
    ;; Var-Var: equal only if same identity
    ((and (var? d1) (var? d2))
     (eq? d1 d2))
    ;; Var-NonVar or NonVar-Var: not equal
    ((or (var? d1) (var? d2))
     #f)
    ;; Integer
    ((and (integer? d1) (integer? d2))
     (eqv? d1 d2))
    ;; Symbol (atom)
    ((and (symbol? d1) (symbol? d2))
     (eq? d1 d2))
    ;; Boolean
    ((and (boolean? d1) (boolean? d2))
     (eq? d1 d2))
    ;; String (text)
    ((and (string? d1) (string? d2))
     (string=? d1 d2))
    ;; Term: same functor, same arity, all args recursively equal
    ((and (term? d1) (term? d2)
          (eq? (term-functor d1) (term-functor d2))
          (= (vector-length (term-args d1))
             (vector-length (term-args d2))))
     (equal-args (term-args d1) (term-args d2) 0))
    ;; Everything else
    (else #f)))

(define (equal-args v1 v2 i)
  (if (>= i (vector-length v1))
      #t
      (if (equal?/chr (vector-ref v1 i) (vector-ref v2 i))
          (equal-args v1 v2 (+ i 1))
          #f)))

;;; --------------------------------------------------------------------------
;;; Term operations
;;; --------------------------------------------------------------------------

(define (match-term v functor arity)
  (let ((d (deref v)))
    (and (term? d)
         (eq? (term-functor d) functor)
         (= (vector-length (term-args d)) arity))))

(define (get-arg v idx)
  (vector-ref (term-args (deref v)) idx))

;;; --------------------------------------------------------------------------
;;; Observer management
;;; --------------------------------------------------------------------------

(define (add-observer! suspension-id v)
  (let ((d (deref v)))
    (when (and (var? d) (eq? (var-value d) *unbound*))
      (var-observers-set! d (cons suspension-id (var-observers d))))))

;;; --------------------------------------------------------------------------
;;; Var ID extraction
;;; --------------------------------------------------------------------------

(define (get-var-id v)
  (let ((d (deref v)))
    (if (and (var? d) (eq? (var-value d) *unbound*))
        (var-id d)
        #f)))
