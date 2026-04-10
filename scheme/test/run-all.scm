;; Driver that runs all SRFI-64 test files in this directory.
;;
;; SRFI-64 reports failures by printing them, but does not change the
;; exit status. This driver installs a custom test-runner factory that
;; accumulates failure counts across every loaded test file, then
;; exits with status 1 if any test failed.
;;
;; Run from this directory so that `(load "test-foo.scm")` resolves
;; correctly and the .log files SRFI-64 writes land here instead of
;; in the project root:
;;
;;   cd scheme/test && guile3.0 -L .. -x .sls run-all.scm

(import (rnrs)
        (srfi :64))

(define total-failures 0)

(define old-factory (test-runner-factory))

(test-runner-factory
 (lambda ()
   (let ((runner (old-factory)))
     (let ((prev (test-runner-on-final runner)))
       (test-runner-on-final! runner
         (lambda (r)
           (set! total-failures
                 (+ total-failures (test-runner-fail-count r)))
           (when prev (prev r)))))
     runner)))

(load "test-var.scm")
(load "test-store.scm")
(load "test-history.scm")
(load "test-reactivation.scm")
(load "test-runtime.scm")

(format #t "~%Total failures: ~a~%" total-failures)
(exit (zero? total-failures))
