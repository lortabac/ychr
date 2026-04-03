(import (rnrs)
        (srfi :64)
        (ychr runtime))

(test-begin "history")

(test-group "empty-history"
  (let ((s (%make-session 0)))
    (test-assert "absent entry" (not-in-history? s 'rule1 '(0 1)))
    (test-assert "absent entry" (not-in-history? s 'rule2 '()))))

(test-group "add-and-check"
  (let ((s (%make-session 0)))
    (add-history! s 'rule1 '(0 1))
    (test-assert "present after add" (not (not-in-history? s 'rule1 '(0 1))))
    (test-assert "other entry still absent" (not-in-history? s 'rule1 '(2 3)))))

(test-group "different-rule-same-ids"
  (let ((s (%make-session 0)))
    (add-history! s 'rule1 '(0 1))
    (test-assert "different rule is absent" (not-in-history? s 'rule2 '(0 1)))))

(test-group "same-rule-different-ids"
  (let ((s (%make-session 0)))
    (add-history! s 'rule1 '(0 1))
    (test-assert "different ids absent" (not-in-history? s 'rule1 '(0 2)))
    (test-assert "different ids absent" (not-in-history? s 'rule1 '(1 0)))))

(test-group "order-matters"
  (let ((s (%make-session 0)))
    (add-history! s 'rule1 '(0 1))
    (test-assert "reversed order is distinct" (not-in-history? s 'rule1 '(1 0)))
    (add-history! s 'rule1 '(1 0))
    (test-assert "both present" (not (not-in-history? s 'rule1 '(0 1))))
    (test-assert "both present" (not (not-in-history? s 'rule1 '(1 0))))))

(test-group "multiple-entries"
  (let ((s (%make-session 0)))
    (add-history! s 'r1 '(0))
    (add-history! s 'r2 '(1 2))
    (add-history! s 'r3 '())
    (test-assert "r1 present" (not (not-in-history? s 'r1 '(0))))
    (test-assert "r2 present" (not (not-in-history? s 'r2 '(1 2))))
    (test-assert "r3 present" (not (not-in-history? s 'r3 '())))
    (test-assert "r1 other absent" (not-in-history? s 'r1 '(1)))
    (test-assert "r2 other absent" (not-in-history? s 'r2 '(2 1)))))

(test-group "idempotent-add"
  (let ((s (%make-session 0)))
    (add-history! s 'rule1 '(5 6))
    (add-history! s 'rule1 '(5 6))
    (test-assert "still present" (not (not-in-history? s 'rule1 '(5 6))))))

(test-end "history")
