(import (scheme base)
        (srfi 64)
        (ychr history))

(test-begin "history")

(test-group "empty-history"
  (init-history!)
  (test-assert "absent entry" (not-in-history? 'rule1 '(0 1)))
  (test-assert "absent entry" (not-in-history? 'rule2 '())))

(test-group "add-and-check"
  (init-history!)
  (add-history! 'rule1 '(0 1))
  (test-assert "present after add" (not (not-in-history? 'rule1 '(0 1))))
  (test-assert "other entry still absent" (not-in-history? 'rule1 '(2 3))))

(test-group "different-rule-same-ids"
  (init-history!)
  (add-history! 'rule1 '(0 1))
  (test-assert "different rule is absent" (not-in-history? 'rule2 '(0 1))))

(test-group "same-rule-different-ids"
  (init-history!)
  (add-history! 'rule1 '(0 1))
  (test-assert "different ids absent" (not-in-history? 'rule1 '(0 2)))
  (test-assert "different ids absent" (not-in-history? 'rule1 '(1 0))))

(test-group "order-matters"
  (init-history!)
  (add-history! 'rule1 '(0 1))
  (test-assert "reversed order is distinct" (not-in-history? 'rule1 '(1 0)))
  (add-history! 'rule1 '(1 0))
  (test-assert "both present" (not (not-in-history? 'rule1 '(0 1))))
  (test-assert "both present" (not (not-in-history? 'rule1 '(1 0)))))

(test-group "multiple-entries"
  (init-history!)
  (add-history! 'r1 '(0))
  (add-history! 'r2 '(1 2))
  (add-history! 'r3 '())
  (test-assert "r1 present" (not (not-in-history? 'r1 '(0))))
  (test-assert "r2 present" (not (not-in-history? 'r2 '(1 2))))
  (test-assert "r3 present" (not (not-in-history? 'r3 '())))
  (test-assert "r1 other absent" (not-in-history? 'r1 '(1)))
  (test-assert "r2 other absent" (not-in-history? 'r2 '(2 1))))

(test-group "idempotent-add"
  (init-history!)
  (add-history! 'rule1 '(5 6))
  (add-history! 'rule1 '(5 6))
  (test-assert "still present" (not (not-in-history? 'rule1 '(5 6)))))

(test-end "history")
