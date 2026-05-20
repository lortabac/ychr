(import (rnrs)
        (srfi :64)
        (ychr runtime)
        (ychr pretty)
        (ychr repl))

;;; --------------------------------------------------------------------------
;;; A mock program-info dispatcher built by hand. Mirrors the shape the
;;; Scheme codegen emits (`(ychr generated <name>)` exports a procedure
;;; that responds to 'init and 'tells), so this test exercises the
;;; helpers without needing the Haskell compiler in the loop.
;;; --------------------------------------------------------------------------

;;; Mock tell: bind the second argument to the first plus one. Lets us
;;; verify that name resolution dispatched to the right procedure and
;;; that fresh-var arguments were threaded through correctly.
(define (mock-tell-succ s x y)
  (%unify s y (+ (deref x) 1)))

;;; Mock tell: bind the second argument to the first doubled.
(define (mock-tell-double s x y)
  (%unify s y (* (deref x) 2)))

(define (mock-program key)
  (case key
    ((init) (%make-session 0))
    ((tells)
     (list (cons "foo:succ/2"  mock-tell-succ)
           ;; Two `bar/2` entries in different modules: short form
           ;; "bar/2" must be reported as ambiguous.
           (cons "foo:bar/2"   mock-tell-succ)
           (cons "baz:bar/2"   mock-tell-double)
           ;; Unique short form "unique/2".
           (cons "foo:unique/2" mock-tell-succ)))
    (else (error 'mock-program "unknown key" key))))

(test-begin "repl")

;;; --------------------------------------------------------------------------
;;; bindings->string formatting
;;; --------------------------------------------------------------------------

(test-group "bindings->string"
  (test-equal "single binding ends with newline"
              "R = 55\n"
              (bindings->string (list (cons 'R 55))))
  (test-equal "empty alist produces empty string"
              ""
              (bindings->string '()))
  (test-equal "sorted alphabetically"
              "A = 1\nB = 2\nC = 3\n"
              (bindings->string (list (cons 'C 3) (cons 'A 1) (cons 'B 2))))
  (let* ((s (%make-session 0))
         (v (make-var s)))
    (test-equal "unbound variable renders as _"
                "X = _\n"
                (bindings->string (list (cons 'X v))))))

;;; --------------------------------------------------------------------------
;;; query: end-to-end dispatch and binding capture
;;; --------------------------------------------------------------------------

(test-group "query qualified name"
  (let ((s (open-session mock-program)))
    (let ((r (make-var s)))
      ;; tell-by-name bypasses the implicit fresh-var handling so we
      ;; can inspect the bound value directly.
      (tell-by-name s "foo:succ/2" 10 r)
      (test-equal "succ(10) binds R to 11" 11 (deref r)))))

(test-group "query unambiguous short name"
  (let ((s (open-session mock-program)))
    (let ((r (make-var s)))
      (tell-by-name s "unique/2" 7 r)
      (test-equal "unique(7) binds R to 8" 8 (deref r)))))

(test-group "query ambiguous short name raises"
  (let ((s (open-session mock-program)))
    (let ((r (make-var s)))
      (test-error "bar/2 is ambiguous"
                  (tell-by-name s "bar/2" 1 r)))))

(test-group "query unknown name raises"
  (let ((s (open-session mock-program)))
    (let ((r (make-var s)))
      (test-error "no such constraint"
                  (tell-by-name s "missing/1" r))
      (test-error "qualified unknown name"
                  (tell-by-name s "foo:nope/1" r)))))

(test-group "query without a program raises"
  ;; Drive the implicit context to #f — the same value the parameter
  ;; holds before any open-session call. dynamic-wind in with-program
  ;; restores the prior value cleanly, so the surrounding tests'
  ;; setup is not perturbed even on the raised-and-caught path.
  (with-program #f
    (test-error "no program registered"
                (let ((s (%make-session 0)))
                  (tell-by-name s "foo/1" 1)))))

(test-end "repl")
