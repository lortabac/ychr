(import (rnrs)
        (rnrs io ports)
        (srfi :64)
        (ychr runtime)
        (ychr pretty)
        (ychr repl))

;;; --------------------------------------------------------------------------
;;; Hand-built mock that mirrors what `(ychr generated <name>)` emits:
;;; a session thunk plus one tell procedure per constraint with friendly
;;; aliases bound to it. The codegen produces both qualified and short
;;; aliases (the latter only when unique within the library); here we
;;; replicate that pattern manually.
;;; --------------------------------------------------------------------------

(define (mock-program) (%make-session 0))

;;; Mock tell: bind the second argument to the first plus one.
(define (tell_foo__succ2 s x y)
  (%unify s y (+ (deref x) 1)))

;;; Mock tell: bind the second argument to the first doubled.
(define (tell_baz__double2 s x y)
  (%unify s y (* (deref x) 2)))

(define foo:succ/2 tell_foo__succ2)
(define succ/2 tell_foo__succ2)
(define baz:double/2 tell_baz__double2)
(define double/2 tell_baz__double2)

;;; Capture everything the body writes to (current-output-port).
;;; `tell` reports bindings via `display`, so checking that channel is
;;; the only way to assert the printed form.
(define (capture-stdout thunk)
  (let-values (((port extract) (open-string-output-port)))
    (parameterize ((current-output-port port))
      (thunk))
    (extract)))

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
;;; open-session
;;; --------------------------------------------------------------------------

(test-group "open-session returns a fresh session"
  (let ((s1 (open-session mock-program))
        (s2 (open-session mock-program)))
    (test-assert "two opens give distinct sessions"
                 (not (eq? s1 s2)))))

;;; --------------------------------------------------------------------------
;;; tell with a qualified alias and a fresh-var placeholder
;;; --------------------------------------------------------------------------

(test-group "tell with qualified alias and fresh-var placeholder"
  (let ((s (open-session mock-program)))
    (test-equal "succ(10, R) prints R = 11"
                "R = 11\n"
                (capture-stdout
                 (lambda () (tell s foo:succ/2 10 'R))))))

;;; --------------------------------------------------------------------------
;;; tell with the short alias
;;; --------------------------------------------------------------------------

(test-group "tell with short alias"
  (let ((s (open-session mock-program)))
    (test-equal "succ(7, R) via short alias"
                "R = 8\n"
                (capture-stdout
                 (lambda () (tell s succ/2 7 'R))))))

;;; --------------------------------------------------------------------------
;;; tell prints nothing when no placeholder is supplied
;;; --------------------------------------------------------------------------

(test-group "tell with no placeholders prints empty string"
  (let* ((s (open-session mock-program))
         (r (make-var s))
         (out (capture-stdout
               (lambda () (tell s foo:succ/2 10 r)))))
    (test-equal "no placeholder => empty output" "" out)
    (test-equal "var was still bound by the tell call" 11 (deref r))))

;;; --------------------------------------------------------------------------
;;; Raw direct-call form (skipping tell): users who want full control
;;; over var lifecycle and output can call the alias as a plain
;;; procedure.
;;; --------------------------------------------------------------------------

(test-group "direct-call form"
  (let* ((s (open-session mock-program))
         (r (make-var s)))
    (foo:succ/2 s 10 r)
    (test-equal "direct call binds r to 11" 11 (deref r))))

(test-end "repl")
