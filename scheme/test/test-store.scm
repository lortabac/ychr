(import (scheme base)
        (scheme write)
        (srfi 64)
        (ychr var)
        (ychr store))

(test-begin "store")

;;; --------------------------------------------------------------------------
;;; Suspension creation
;;; --------------------------------------------------------------------------

(test-group "create-constraint"
  (init-store! 3)
  (reset-var-counter!)

  (let* ((s1 (create-constraint 0 (vector 1 2)))
         (s2 (create-constraint 1 (vector 'a))))
    (test-assert "returns a suspension" (suspension? s1))
    (test-assert "distinct suspensions" (not (eq? s1 s2)))
    (test-eqv "sequential ids" 0 (suspension-id s1))
    (test-eqv "sequential ids" 1 (suspension-id s2))
    (test-eqv "type preserved" 0 (suspension-type s1))
    (test-eqv "type preserved" 1 (suspension-type s2))
    (test-eqv "arg access" 1 (suspension-arg s1 0))
    (test-eqv "arg access" 2 (suspension-arg s1 1))
    (test-eq "arg access" 'a (suspension-arg s2 0))
    (test-assert "alive by default" (suspension-alive? s1))))

;;; --------------------------------------------------------------------------
;;; Store and snapshot
;;; --------------------------------------------------------------------------

(test-group "store-and-snapshot"
  (init-store! 2)
  (reset-var-counter!)

  (test-group "empty snapshot"
    (let-values (((vec count) (store-snapshot 0)))
      (test-eqv "count is 0" 0 count)))

  (test-group "store adds to snapshot"
    (let ((s1 (create-constraint 0 (vector 10)))
          (s2 (create-constraint 0 (vector 20)))
          (s3 (create-constraint 1 (vector 30))))
      (store-constraint s1)
      (store-constraint s2)
      (store-constraint s3)
      ;; Type 0 has 2 suspensions
      (let-values (((vec count) (store-snapshot 0)))
        (test-eqv "type 0 count" 2 count)
        (test-eq "first suspension" s1 (snapshot-ref vec 0))
        (test-eq "second suspension" s2 (snapshot-ref vec 1)))
      ;; Type 1 has 1 suspension
      (let-values (((vec count) (store-snapshot 1)))
        (test-eqv "type 1 count" 1 count)
        (test-eq "suspension" s3 (snapshot-ref vec 0)))))

  (test-group "snapshot is a snapshot"
    (init-store! 1)
    (let ((s1 (create-constraint 0 (vector 1))))
      (store-constraint s1)
      (let-values (((vec count) (store-snapshot 0)))
        ;; Add another constraint after snapshot
        (let ((s2 (create-constraint 0 (vector 2))))
          (store-constraint s2)
          ;; Snapshot count should still be 1
          (test-eqv "snapshot frozen" 1 count)
          ;; But a new snapshot sees both
          (let-values (((vec2 count2) (store-snapshot 0)))
            (test-eqv "new snapshot sees both" 2 count2)))))))

;;; --------------------------------------------------------------------------
;;; Kill and alive
;;; --------------------------------------------------------------------------

(test-group "kill-and-alive"
  (init-store! 1)
  (reset-var-counter!)

  (let ((s (create-constraint 0 (vector 42))))
    (store-constraint s)
    (test-assert "alive initially" (alive-constraint? s))
    (kill-constraint s)
    (test-assert "dead after kill" (not (alive-constraint? s)))
    ;; Suspension is still in the store, just marked dead
    (let-values (((vec count) (store-snapshot 0)))
      (test-eqv "still in store" 1 count)
      (test-assert "but dead" (not (suspension-alive? (snapshot-ref vec 0)))))))

;;; --------------------------------------------------------------------------
;;; Constraint accessors
;;; --------------------------------------------------------------------------

(test-group "constraint-accessors"
  (init-store! 2)
  (reset-var-counter!)

  (let ((s (create-constraint 1 (vector 'x 'y 'z))))
    (test-eqv "constraint-arg 0" 'x (constraint-arg s 0))
    (test-eqv "constraint-arg 1" 'y (constraint-arg s 1))
    (test-eqv "constraint-arg 2" 'z (constraint-arg s 2))
    (test-eqv "constraint-id" 0 (constraint-id s))
    (test-eqv "constraint-type" 1 (constraint-type s))))

;;; --------------------------------------------------------------------------
;;; Identity comparison
;;; --------------------------------------------------------------------------

(test-group "id-equal"
  (init-store! 1)
  (reset-var-counter!)

  (let ((s1 (create-constraint 0 (vector 1)))
        (s2 (create-constraint 0 (vector 1))))
    (test-assert "same suspension" (id-equal? s1 s1))
    (test-assert "different suspensions" (not (id-equal? s1 s2)))))

;;; --------------------------------------------------------------------------
;;; Type checking
;;; --------------------------------------------------------------------------

(test-group "is-constraint-type"
  (init-store! 3)
  (reset-var-counter!)

  (let ((s (create-constraint 2 (vector 'a))))
    (test-assert "correct type" (is-constraint-type? s 2))
    (test-assert "wrong type" (not (is-constraint-type? s 0)))
    (test-assert "wrong type" (not (is-constraint-type? s 1)))))

;;; --------------------------------------------------------------------------
;;; Observer registration on store
;;; --------------------------------------------------------------------------

(test-group "observer-registration"
  (init-store! 1)
  (reset-var-counter!)

  (test-group "variable args get observers"
    (let ((x (make-var))
          (y (make-var)))
      (let ((s (create-constraint 0 (vector x 42 y))))
        (store-constraint s)
        ;; Binding x should emit observer for s (as a suspension record)
        (let-values (((ok obs) (unify x 1)))
          (test-assert "unify succeeds" ok)
          (test-assert "observer emitted for x"
            (memq s obs)))
        ;; Binding y should emit observer for s
        (let-values (((ok obs) (unify y 2)))
          (test-assert "unify succeeds" ok)
          (test-assert "observer emitted for y"
            (memq s obs))))))

  (test-group "ground args do not register observers"
    (let ((s (create-constraint 0 (vector 1 'a #t))))
      (store-constraint s)
      ;; No variables to observe — nothing should break
      (test-assert "no error" #t)))

  (test-group "already-bound vars do not register observers"
    (let ((x (make-var)))
      (unify x 99)
      (let ((s (create-constraint 0 (vector x))))
        (store-constraint s)
        ;; x is already bound, so no observer should be registered.
        ;; We cannot easily test the absence of an observer, but
        ;; we verify no error occurs.
        (test-assert "no error" #t)))))

;;; --------------------------------------------------------------------------
;;; Growable vector stress
;;; --------------------------------------------------------------------------

(test-group "growable-growth"
  (init-store! 1)
  (reset-var-counter!)

  ;; Push more constraints than the initial capacity (16) to trigger growth
  (let loop ((i 0) (susps '()))
    (if (< i 50)
        (let ((s (create-constraint 0 (vector i))))
          (store-constraint s)
          (loop (+ i 1) (cons s susps)))
        (let-values (((vec count) (store-snapshot 0)))
          (test-eqv "all 50 stored" 50 count)
          ;; Verify first and last
          (test-eqv "first arg" 0 (suspension-arg (snapshot-ref vec 0) 0))
          (test-eqv "last arg" 49 (suspension-arg (snapshot-ref vec 49) 0))))))

(test-end "store")
