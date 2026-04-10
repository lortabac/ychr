(import (rnrs)
        (srfi :64)
        (ychr runtime))

(define (fresh-session) (%make-session 0))

(test-begin "runtime")

;;; --------------------------------------------------------------------------
;;; %unify success cases
;;; --------------------------------------------------------------------------

(test-group "%unify success"
  (test-assert "atom = atom"
               (%unify (fresh-session) 'a 'a))
  (test-assert "int = int"
               (%unify (fresh-session) 1 1))
  (let* ((s (fresh-session))
         (x (make-var s)))
    (test-assert "var = int" (%unify s x 1))))

;;; --------------------------------------------------------------------------
;;; %unify failure raises a runtime error
;;; --------------------------------------------------------------------------

(test-group "%unify failure raises"
  (test-error "int mismatch"
              (%unify (fresh-session) 1 2))
  (test-error "atom mismatch"
              (%unify (fresh-session) 'foo 'bar))
  (test-error "list length mismatch"
              (let* ((s (fresh-session))
                     (x (make-var s))
                     (y (make-var s))
                     (lhs (%cons x (%cons y (%nil))))
                     (rhs (%cons 1 (%cons 2 (%cons 3 (%nil))))))
                (%unify s lhs rhs))))

(test-end "runtime")
