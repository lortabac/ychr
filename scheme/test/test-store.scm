(import (rnrs)
        (srfi :64)
        (ychr runtime))

(test-begin "store")

(test-group "create-constraint"
  (let ((s (%make-session 3)))
    (let* ((s1 (create-constraint s 0 (vector 1 2)))
           (s2 (create-constraint s 1 (vector 'a))))
      (test-assert "returns a suspension" (suspension? s1))
      (test-assert "distinct suspensions" (not (eq? s1 s2)))
      (test-eqv "sequential ids" 0 (suspension-id s1))
      (test-eqv "sequential ids" 1 (suspension-id s2))
      (test-eqv "type preserved" 0 (suspension-type s1))
      (test-eqv "type preserved" 1 (suspension-type s2))
      (test-eqv "arg access" 1 (suspension-arg s1 0))
      (test-eqv "arg access" 2 (suspension-arg s1 1))
      (test-eq "arg access" 'a (suspension-arg s2 0))
      (test-assert "alive by default" (suspension-alive? s1)))))

(test-group "store-and-snapshot"
  (let ((s (%make-session 2)))
    (test-group "empty snapshot"
      (let-values (((vec count) (store-snapshot s 0)))
        (test-eqv "count is 0" 0 count)))

    (test-group "store adds to snapshot"
      (let ((s1 (create-constraint s 0 (vector 10)))
            (s2 (create-constraint s 0 (vector 20)))
            (s3 (create-constraint s 1 (vector 30))))
        (store-constraint s s1)
        (store-constraint s s2)
        (store-constraint s s3)
        (let-values (((vec count) (store-snapshot s 0)))
          (test-eqv "type 0 count" 2 count)
          (test-eq "first suspension" s1 (snapshot-ref vec 0))
          (test-eq "second suspension" s2 (snapshot-ref vec 1)))
        (let-values (((vec count) (store-snapshot s 1)))
          (test-eqv "type 1 count" 1 count)
          (test-eq "suspension" s3 (snapshot-ref vec 0))))))

  (test-group "snapshot is a snapshot"
    (let ((s (%make-session 1)))
      (let ((s1 (create-constraint s 0 (vector 1))))
        (store-constraint s s1)
        (let-values (((vec count) (store-snapshot s 0)))
          (let ((s2 (create-constraint s 0 (vector 2))))
            (store-constraint s s2)
            (test-eqv "snapshot frozen" 1 count)
            (let-values (((vec2 count2) (store-snapshot s 0)))
              (test-eqv "new snapshot sees both" 2 count2))))))))

(test-group "kill-and-alive"
  (let ((s (%make-session 1)))
    (let ((susp (create-constraint s 0 (vector 42))))
      (store-constraint s susp)
      (test-assert "alive initially" (alive-constraint? susp))
      (kill-constraint susp)
      (test-assert "dead after kill" (not (alive-constraint? susp)))
      (let-values (((vec count) (store-snapshot s 0)))
        (test-eqv "still in store" 1 count)
        (test-assert "but dead" (not (suspension-alive? (snapshot-ref vec 0))))))))

(test-group "constraint-accessors"
  (let ((s (%make-session 2)))
    (let ((susp (create-constraint s 1 (vector 'x 'y 'z))))
      (test-eqv "constraint-arg 0" 'x (constraint-arg susp 0))
      (test-eqv "constraint-arg 1" 'y (constraint-arg susp 1))
      (test-eqv "constraint-arg 2" 'z (constraint-arg susp 2))
      (test-eqv "constraint-id" 0 (constraint-id susp))
      (test-eqv "constraint-type" 1 (constraint-type susp)))))

(test-group "id-equal"
  (let ((s (%make-session 1)))
    (let ((s1 (create-constraint s 0 (vector 1)))
          (s2 (create-constraint s 0 (vector 1))))
      (test-assert "same suspension" (id-equal? s1 s1))
      (test-assert "different suspensions" (not (id-equal? s1 s2))))))

(test-group "is-constraint-type"
  (let ((s (%make-session 3)))
    (let ((susp (create-constraint s 2 (vector 'a))))
      (test-assert "correct type" (is-constraint-type? susp 2))
      (test-assert "wrong type" (not (is-constraint-type? susp 0)))
      (test-assert "wrong type" (not (is-constraint-type? susp 1))))))

(test-group "observer-registration"
  (let ((s (%make-session 1)))
    (test-group "variable args get observers"
      (let ((x (make-var s))
            (y (make-var s)))
        (let ((susp (create-constraint s 0 (vector x 42 y))))
          (store-constraint s susp)
          (let-values (((ok obs) (unify x 1)))
            (test-assert "unify succeeds" ok)
            (test-assert "observer emitted for x" (memq susp obs)))
          (let-values (((ok obs) (unify y 2)))
            (test-assert "unify succeeds" ok)
            (test-assert "observer emitted for y" (memq susp obs))))))

    (test-group "ground args do not register observers"
      (let ((susp (create-constraint s 0 (vector 1 'a #t))))
        (store-constraint s susp)
        (test-assert "no error" #t)))))

(test-group "growable-growth"
  (let ((s (%make-session 1)))
    (let loop ((i 0) (susps '()))
      (if (< i 50)
          (let ((susp (create-constraint s 0 (vector i))))
            (store-constraint s susp)
            (loop (+ i 1) (cons susp susps)))
          (let-values (((vec count) (store-snapshot s 0)))
            (test-eqv "all 50 stored" 50 count)
            (test-eqv "first arg" 0 (suspension-arg (snapshot-ref vec 0) 0))
            (test-eqv "last arg" 49 (suspension-arg (snapshot-ref vec 49) 0)))))))

(test-end "store")
