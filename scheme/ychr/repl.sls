;;;; User-facing helpers for interactive CHR programs in Scheme.
;;;;
;;;; The typical session shape is:
;;;;
;;;;   (import (ychr) (ychr generated fib))
;;;;   (define s (open-session fib))
;;;;   (tell s fib:fib/2 10 'R)
;;;;   ;; => R = 55
;;;;
;;;; `open-session` invokes the program's session thunk (the binding
;;;; named after the library's final segment) and returns a fresh CHR
;;;; session.
;;;;
;;;; `tell` takes a tell procedure directly — the generated library
;;;; exports two identifier aliases per constraint, e.g. `fib:fib/2`
;;;; (qualified) and `fib/2` (short, when unique within the library).
;;;; Resolution happens at Scheme expand time, so there is no per-call
;;;; runtime lookup.
;;;;
;;;; Arguments that are uppercase-or-underscore-initial symbols (`'R`,
;;;; `'_X`) become fresh logical variables and are reported in the
;;;; printed bindings; other arguments are passed through unchanged.
(library (ychr repl)
  (export open-session tell)
  (import (rnrs) (ychr runtime) (ychr pretty))

  (define (open-session prog) (prog))

  ;; A symbol starting with `_` or an uppercase ASCII letter is treated
  ;; as a fresh-variable placeholder. Matches the Prolog convention:
  ;; lowercase-initial symbols are atoms.
  (define (var-name? sym)
    (and (symbol? sym)
         (let ((s (symbol->string sym)))
           (and (> (string-length s) 0)
                (let ((c (string-ref s 0)))
                  (or (char=? c #\_)
                      (and (char<=? #\A c) (char<=? c #\Z))))))))

  ;; Walk the user-supplied argument list, replacing variable-name
  ;; symbols with fresh logical variables. Returns two values: the
  ;; argument list to pass on, and an alist of (sym . var) pairs to
  ;; print after the call.
  (define (process-args session args)
    (let loop ((args args) (out '()) (binds '()))
      (cond
        ((null? args) (values (reverse out) (reverse binds)))
        ((var-name? (car args))
         (let ((v (make-var session)))
           (loop (cdr args)
                 (cons v out)
                 (cons (cons (car args) v) binds))))
        (else (loop (cdr args) (cons (car args) out) binds)))))

  (define (tell session proc . args)
    (let-values (((processed binds) (process-args session args)))
      (apply proc session processed)
      (pretty-bindings binds)))
)
