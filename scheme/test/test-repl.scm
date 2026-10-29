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

;;; Mock: y := x+1, z := x*2.
(define (tell_qux__pair3 s x y z)
  (%unify s y (+ (deref x) 1))
  (%unify s z (* (deref x) 2)))

;;; Mock: y := x+1, z := y (proves y got bound).
(define (tell_qux__chain3 s x y z)
  (%unify s y (+ (deref x) 1))
  (%unify s z (deref y)))

;;; Mock: saves its two args so a test can check if they're the same object.
(define captured #f)
(define (tell_qux__capture2 s x y)
  (set! captured (list x y)))

(define (captured-same?)
  (eq? (car captured) (cadr captured)))

;;; Mock: unifies its two args directly, leaving both unbound and
;;; aliased to each other.
(define (tell_qux__same2 s x y) (%unify s x y))

(define foo:succ/2 tell_foo__succ2)
(define succ/2 tell_foo__succ2)
(define baz:double/2 tell_baz__double2)
(define double/2 tell_baz__double2)
(define qux:pair/3 tell_qux__pair3)
(define qux:chain/3 tell_qux__chain3)
(define qux:capture/2 tell_qux__capture2)
(define qux:same/2 tell_qux__same2)

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
                (bindings->string (list (cons 'X v)))))
  (let* ((s (%make-session 0))
         (v1 (make-var s))
         (v2 (make-var s)))
    (test-equal "two distinct unbound vars are singletons, both print _"
                "A = _\nB = _\n"
                (bindings->string (list (cons 'A v1) (cons 'B v2)))))
  (let* ((s (%make-session 0))
         (v (make-var s)))
    (test-equal "two vars sharing an id print as each other"
                "A = B\nB = A\n"
                (bindings->string (list (cons 'A v) (cons 'B v)))))
  (let* ((s (%make-session 0))
         (v (make-var s)))
    (test-equal "three vars sharing an id wrap around"
                "A = B\nB = C\nC = A\n"
                (bindings->string (list (cons 'A v) (cons 'B v) (cons 'C v)))))
  (let* ((s (%make-session 0))
         (v (make-var s))
         (term-a (make-term 'f (vector v))))
    (test-equal "a compound holding an aliased var shows its canonical name"
                "A = f(B)\nB = C\nC = B\n"
                (bindings->string (list (cons 'A term-a) (cons 'B v) (cons 'C v)))))
  (let* ((s (%make-session 0))
         (v (make-var s)))
    (test-equal "a _-prefixed name is dropped and does not join a class"
                "B = _\n"
                (bindings->string (list (cons '_A v) (cons 'B v))))))

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
;;; tell hides `_`-prefixed bindings from the printed output (same
;;; convention as the REPL and `--show-bindings`), but still makes and
;;; binds the variable.
;;; --------------------------------------------------------------------------

(test-group "tell hides a _-prefixed output but still binds it"
  (let* ((s (open-session mock-program))
         (z (make-var s))
         (out (capture-stdout
               (lambda () (tell s qux:chain/3 10 '_Y z)))))
    (test-equal "_-prefixed binding is not printed" "" out)
    (test-equal "_Y was bound" 11 (deref z))))

(test-group "tell mixes visible and hidden outputs"
  (let ((s (open-session mock-program)))
    (test-equal "only the visible one prints"
                "R = 11\n"
                (capture-stdout
                 (lambda () (tell s qux:pair/3 10 'R '_D))))))

;;; --------------------------------------------------------------------------
;;; tell shares one variable for a symbol repeated in the same call,
;;; but never shares across two bare `_`.
;;; --------------------------------------------------------------------------

(test-group "tell shares repeated symbols, but not bare _"
  (let ((s (open-session mock-program)))
    (capture-stdout (lambda () (tell s qux:capture/2 'R 'R)))
    (test-assert "'R 'R is the same variable" (captured-same?)))
  (let ((s (open-session mock-program)))
    (capture-stdout (lambda () (tell s qux:capture/2 '_ '_)))
    (test-assert "'_ '_ is not the same variable" (not (captured-same?))))
  (let ((s (open-session mock-program)))
    (capture-stdout (lambda () (tell s qux:capture/2 '_X '_X)))
    (test-assert "'_X '_X is the same variable" (captured-same?))))

(test-group "tell prints one line for a repeated symbol"
  (let ((s (open-session mock-program)))
    (test-equal "chain(10, R, R) prints R once"
                "R = 11\n"
                (capture-stdout
                 (lambda () (tell s qux:chain/3 10 'R 'R))))))

;;; --------------------------------------------------------------------------
;;; tell prints aliased unbound vars as each other (A = B, B = A).
;;; --------------------------------------------------------------------------

(test-group "tell prints unified-but-unbound vars as each other"
  (let ((s (open-session mock-program)))
    (test-equal "same(A, B) prints A = B, B = A"
                "A = B\nB = A\n"
                (capture-stdout
                 (lambda () (tell s qux:same/2 'A 'B))))))

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
