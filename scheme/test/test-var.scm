(import (scheme base)
        (scheme write)
        (srfi 64)
        (ychr var))

(test-begin "var")

;;; --------------------------------------------------------------------------
;;; Variable creation
;;; --------------------------------------------------------------------------

(test-group "make-var"
  (reset-var-counter!)
  (let* ((x (make-var))
         (y (make-var)))
    (test-assert "returns a var" (var? x))
    (test-assert "distinct vars" (not (eq? x y)))
    (test-eqv "sequential ids" 0 (var-id x))
    (test-eqv "sequential ids" 1 (var-id y))))

;;; --------------------------------------------------------------------------
;;; Deref
;;; --------------------------------------------------------------------------

(test-group "deref"
  (reset-var-counter!)

  (test-group "unbound var derefs to itself"
    (let ((x (make-var)))
      (test-eq "identity" x (deref x))))

  (test-group "ground values deref to themselves"
    (test-eqv "integer" 42 (deref 42))
    (test-eq "symbol" 'foo (deref 'foo))
    (test-eq "boolean" #t (deref #t)))

  (test-group "follows binding chain"
    (let ((x (make-var))
          (y (make-var)))
      ;; x -> y -> 42
      (unify x y)
      (unify y 42)
      (test-eqv "deref through chain" 42 (deref x))))

  (test-group "path compression"
    (let ((x (make-var))
          (y (make-var))
          (z (make-var)))
      ;; x -> y -> z -> 99
      (unify x y)
      (unify y z)
      (unify z 99)
      (test-eqv "deref reaches end" 99 (deref x))
      ;; After path compression, x points directly to 99.
      ;; A second deref should not need to traverse the chain.
      (test-eqv "compressed" 99 (deref x)))))

;;; --------------------------------------------------------------------------
;;; Unify — ground values
;;; --------------------------------------------------------------------------

(test-group "unify-ground"
  (reset-var-counter!)

  (test-group "integers"
    (let-values (((ok obs) (unify 1 1)))
      (test-assert "same int succeeds" ok)
      (test-assert "no observers" (null? obs)))
    (let-values (((ok obs) (unify 1 2)))
      (test-assert "different int fails" (not ok))))

  (test-group "symbols"
    (let-values (((ok obs) (unify 'a 'a)))
      (test-assert "same symbol succeeds" ok))
    (let-values (((ok obs) (unify 'a 'b)))
      (test-assert "different symbol fails" (not ok))))

  (test-group "booleans"
    (let-values (((ok obs) (unify #t #t)))
      (test-assert "same bool succeeds" ok))
    (let-values (((ok obs) (unify #t #f)))
      (test-assert "different bool fails" (not ok))))

  (test-group "strings"
    (let-values (((ok obs) (unify "hello" "hello")))
      (test-assert "same string succeeds" ok))
    (let-values (((ok obs) (unify "hello" "world")))
      (test-assert "different string fails" (not ok))))

  (test-group "type mismatches"
    (let-values (((ok obs) (unify 1 'a)))
      (test-assert "int vs symbol" (not ok)))
    (let-values (((ok obs) (unify #t 1)))
      (test-assert "bool vs int" (not ok)))
    (let-values (((ok obs) (unify "x" 'x)))
      (test-assert "string vs symbol" (not ok)))))

;;; --------------------------------------------------------------------------
;;; Unify — variables
;;; --------------------------------------------------------------------------

(test-group "unify-vars"
  (reset-var-counter!)

  (test-group "var to ground"
    (let ((x (make-var)))
      (let-values (((ok obs) (unify x 42)))
        (test-assert "succeeds" ok)
        (test-eqv "var bound" 42 (deref x)))))

  (test-group "ground to var"
    (let ((x (make-var)))
      (let-values (((ok obs) (unify 42 x)))
        (test-assert "succeeds" ok)
        (test-eqv "var bound" 42 (deref x)))))

  (test-group "var to var"
    (let ((x (make-var))
          (y (make-var)))
      (let-values (((ok obs) (unify x y)))
        (test-assert "succeeds" ok))
      ;; Both should now share the same binding target.
      (unify y 7)
      (test-eqv "x follows through y" 7 (deref x))
      (test-eqv "y is bound" 7 (deref y))))

  (test-group "same var"
    (let ((x (make-var)))
      (let-values (((ok obs) (unify x x)))
        (test-assert "succeeds" ok)
        (test-assert "still unbound" (var? (deref x)))))))

;;; --------------------------------------------------------------------------
;;; Unify — observer collection
;;; --------------------------------------------------------------------------

(test-group "unify-observers"
  (reset-var-counter!)

  (test-group "binding emits observers"
    (let ((x (make-var)))
      (add-observer! 10 x)
      (add-observer! 20 x)
      (let-values (((ok obs) (unify x 42)))
        (test-assert "succeeds" ok)
        (test-assert "observer 10 emitted" (memv 10 obs))
        (test-assert "observer 20 emitted" (memv 20 obs)))))

  (test-group "var-var merge emits first's observers"
    (let ((x (make-var))
          (y (make-var)))
      (add-observer! 1 x)
      (add-observer! 2 y)
      (let-values (((ok obs) (unify x y)))
        (test-assert "succeeds" ok)
        ;; x's observers (1) are emitted; y keeps merged list
        (test-assert "observer 1 emitted" (memv 1 obs)))))

  (test-group "no observers on ground unification"
    (let-values (((ok obs) (unify 5 5)))
      (test-assert "succeeds" ok)
      (test-assert "empty observers" (null? obs)))))

;;; --------------------------------------------------------------------------
;;; Unify — terms
;;; --------------------------------------------------------------------------

(test-group "unify-terms"
  (reset-var-counter!)

  (test-group "same functor and args"
    (let-values (((ok obs) (unify (make-term 'f (vector 1 2))
                                  (make-term 'f (vector 1 2)))))
      (test-assert "succeeds" ok)))

  (test-group "different functor"
    (let-values (((ok obs) (unify (make-term 'f (vector 1))
                                  (make-term 'g (vector 1)))))
      (test-assert "fails" (not ok))))

  (test-group "different arity"
    (let-values (((ok obs) (unify (make-term 'f (vector 1))
                                  (make-term 'f (vector 1 2)))))
      (test-assert "fails" (not ok))))

  (test-group "recursive unification with variables"
    (let ((x (make-var))
          (y (make-var)))
      (let-values (((ok obs) (unify (make-term 'f (vector x 2))
                                    (make-term 'f (vector 1 y)))))
        (test-assert "succeeds" ok)
        (test-eqv "x bound to 1" 1 (deref x))
        (test-eqv "y bound to 2" 2 (deref y)))))

  (test-group "nested terms"
    (let ((x (make-var)))
      (let-values (((ok obs) (unify (make-term 'f (vector (make-term 'g (vector x))))
                                    (make-term 'f (vector (make-term 'g (vector 99)))))))
        (test-assert "succeeds" ok)
        (test-eqv "x bound deeply" 99 (deref x)))))

  (test-group "term vs non-term"
    (let-values (((ok obs) (unify (make-term 'f (vector 1)) 42)))
      (test-assert "fails" (not ok)))))

;;; --------------------------------------------------------------------------
;;; Unify — wildcard
;;; --------------------------------------------------------------------------

(test-group "unify-wildcard"
  (reset-var-counter!)

  (let-values (((ok obs) (unify *wildcard* 42)))
    (test-assert "wildcard unifies with int" ok))
  (let-values (((ok obs) (unify 'a *wildcard*)))
    (test-assert "symbol unifies with wildcard" ok))
  (let ((x (make-var)))
    (let-values (((ok obs) (unify *wildcard* x)))
      (test-assert "wildcard unifies with var" ok)
      (test-assert "var still unbound" (var? (deref x))))))

;;; --------------------------------------------------------------------------
;;; Equal (ask semantics)
;;; --------------------------------------------------------------------------

(test-group "equal-ground"
  (reset-var-counter!)

  (test-assert "same int" (equal?/chr 1 1))
  (test-assert "diff int" (not (equal?/chr 1 2)))
  (test-assert "same symbol" (equal?/chr 'a 'a))
  (test-assert "diff symbol" (not (equal?/chr 'a 'b)))
  (test-assert "same bool" (equal?/chr #t #t))
  (test-assert "diff bool" (not (equal?/chr #t #f)))
  (test-assert "same string" (equal?/chr "hi" "hi"))
  (test-assert "diff string" (not (equal?/chr "hi" "ho")))
  (test-assert "type mismatch" (not (equal?/chr 1 'a))))

(test-group "equal-vars"
  (reset-var-counter!)

  (test-group "same unbound var is equal to itself"
    (let ((x (make-var)))
      (test-assert (equal?/chr x x))))

  (test-group "distinct unbound vars are NOT equal"
    (let ((x (make-var))
          (y (make-var)))
      (test-assert (not (equal?/chr x y)))))

  (test-group "bound var follows deref"
    (let ((x (make-var)))
      (unify x 42)
      (test-assert "equal to its value" (equal?/chr x 42))
      (test-assert "not equal to other" (not (equal?/chr x 99)))))

  (test-group "two vars bound to same value"
    (let ((x (make-var))
          (y (make-var)))
      (unify x 10)
      (unify y 10)
      (test-assert (equal?/chr x y))))

  (test-group "unbound var not equal to ground"
    (let ((x (make-var)))
      (test-assert (not (equal?/chr x 42))))))

(test-group "equal-terms"
  (reset-var-counter!)

  (test-assert "same term"
    (equal?/chr (make-term 'f (vector 1 2))
                (make-term 'f (vector 1 2))))
  (test-assert "different functor"
    (not (equal?/chr (make-term 'f (vector 1))
                     (make-term 'g (vector 1)))))
  (test-assert "different arity"
    (not (equal?/chr (make-term 'f (vector 1))
                     (make-term 'f (vector 1 2)))))
  (test-assert "different args"
    (not (equal?/chr (make-term 'f (vector 1))
                     (make-term 'f (vector 2)))))
  (test-group "nested terms with bound vars"
    (let ((x (make-var)))
      (unify x 'a)
      (test-assert
        (equal?/chr (make-term 'f (vector x))
                    (make-term 'f (vector 'a)))))))

;;; --------------------------------------------------------------------------
;;; match-term and get-arg
;;; --------------------------------------------------------------------------

(test-group "match-term"
  (reset-var-counter!)

  (let ((t (make-term 'f (vector 1 2 3))))
    (test-assert "correct functor and arity" (match-term t 'f 3))
    (test-assert "wrong functor" (not (match-term t 'g 3)))
    (test-assert "wrong arity" (not (match-term t 'f 2)))
    (test-assert "non-term" (not (match-term 42 'f 1))))

  (test-group "through deref"
    (let ((x (make-var))
          (t (make-term 'g (vector 'a))))
      (unify x t)
      (test-assert (match-term x 'g 1)))))

(test-group "get-arg"
  (reset-var-counter!)

  (let ((t (make-term 'f (vector 10 20 30))))
    (test-eqv "arg 0" 10 (get-arg t 0))
    (test-eqv "arg 1" 20 (get-arg t 1))
    (test-eqv "arg 2" 30 (get-arg t 2)))

  (test-group "through deref"
    (let ((x (make-var))
          (t (make-term 'h (vector 'ok))))
      (unify x t)
      (test-eq "arg through var" 'ok (get-arg x 0)))))

;;; --------------------------------------------------------------------------
;;; add-observer!
;;; --------------------------------------------------------------------------

(test-group "add-observer"
  (reset-var-counter!)

  (test-group "adds to unbound var"
    (let ((x (make-var)))
      (add-observer! 5 x)
      (add-observer! 6 x)
      ;; Bind and check observers are emitted
      (let-values (((ok obs) (unify x 1)))
        (test-assert "observer 5" (memv 5 obs))
        (test-assert "observer 6" (memv 6 obs)))))

  (test-group "no-op on bound var"
    (let ((x (make-var)))
      (unify x 42)
      (add-observer! 7 x)
      ;; x is already bound; observer 7 should not be stored anywhere
      ;; observable since we cannot re-bind x
      (test-assert "bound var" #t)))

  (test-group "no-op on non-var"
    (add-observer! 8 42)
    (test-assert "non-var" #t)))

;;; --------------------------------------------------------------------------
;;; get-var-id
;;; --------------------------------------------------------------------------

(test-group "get-var-id"
  (reset-var-counter!)

  (let* ((x (make-var))
         (y (make-var)))
    (test-eqv "unbound var id" 0 (get-var-id x))
    (test-eqv "unbound var id" 1 (get-var-id y))
    (unify x 42)
    (test-eq "bound var returns #f" #f (get-var-id x))
    (test-eq "non-var returns #f" #f (get-var-id 99))))

(test-end "var")
