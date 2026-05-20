;;;; User-facing helpers for interactive CHR programs in Scheme.
;;;;
;;;; The typical session shape is:
;;;;
;;;;   (import (ychr) (ychr generated fib))
;;;;   (define s (open-session fib))
;;;;   (query s "fib/2" 10 'R)
;;;;   ;; => R = 55
;;;;
;;;; `open-session` registers the program info (the dispatcher closure
;;;; exported by every generated `(ychr generated <name>)` library) as
;;;; the implicit context for `query` and returns a fresh CHR session.
;;;;
;;;; `query` accepts a constraint name in either qualified
;;;; (`"mod:name/arity"`) or unambiguous-short (`"name/arity"`) form.
;;;; Arguments that are uppercase-or-underscore-initial symbols (`'R`,
;;;; `'_X`) become fresh logical variables and are reported in the
;;;; printed bindings; other arguments are passed through unchanged.
(library (ychr repl)
  (export open-session query tell-by-name with-program)
  (import (rnrs) (ychr runtime) (ychr pretty))

  ;; Implicit program context for `query` / `tell-by-name`. Holds the
  ;; dispatcher closure exported by a generated library. Use
  ;; `with-program` to scope a different program temporarily.
  ;;
  ;; R6RS `(rnrs)` does not portably expose `make-parameter` from
  ;; library code (it's a top-level/SRFI-39 extension in both Chez and
  ;; Guile r6rs), so we implement parameter-like behaviour with a
  ;; single mutable cell plus `dynamic-wind`.
  (define *current-program* #f)
  (define (current-program) *current-program*)

  (define (open-session prog)
    (set! *current-program* prog)
    (prog 'init))

  (define-syntax with-program
    (syntax-rules ()
      ((_ prog body0 body ...)
       (let ((saved *current-program*) (new-prog prog))
         (dynamic-wind
           (lambda () (set! *current-program* new-prog))
           (lambda () body0 body ...)
           (lambda () (set! *current-program* saved)))))))

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

  (define (lookup-assoc key tells)
    (cond
      ((null? tells) #f)
      ((string=? key (caar tells)) (car tells))
      (else (lookup-assoc key (cdr tells)))))

  (define (qualified-key? name)
    (let loop ((i 0))
      (cond
        ((>= i (string-length name)) #f)
        ((char=? #\: (string-ref name i)) #t)
        (else (loop (+ i 1))))))

  (define (qualified-ends-with? key short)
    (let ((kl (string-length key)) (sl (string-length short)))
      (and (> kl sl)
           (char=? #\: (string-ref key (- kl sl 1)))
           (string=? (substring key (- kl sl) kl) short))))

  (define (string-join sep strs)
    (cond
      ((null? strs) "")
      ((null? (cdr strs)) (car strs))
      (else (string-append (car strs) sep (string-join sep (cdr strs))))))

  ;; Resolve a friendly name string against the program's tell-procedure
  ;; alist, returning the procedure to call. Qualified names must match
  ;; exactly. Unqualified short names succeed when exactly one
  ;; qualified entry has the suffix `:name/arity`; multiple candidates
  ;; raise an error listing them so the caller can disambiguate.
  (define (resolve-tell-name name tells)
    (let ((direct (lookup-assoc name tells)))
      (cond
        (direct (cdr direct))
        ((qualified-key? name)
         (error 'query
                (string-append "no constraint named " name)))
        (else
         (let ((matches (filter
                         (lambda (entry)
                           (qualified-ends-with? (car entry) name))
                         tells)))
           (cond
             ((null? matches)
              (error 'query
                     (string-append "no constraint named " name)))
             ((null? (cdr matches))
              (cdar matches))
             (else
              (error 'query
                     (string-append "ambiguous short name '" name
                                    "' (candidates: "
                                    (string-join ", " (map car matches))
                                    "); use the qualified form")))))))))

  (define (current-tells)
    (let ((prog (current-program)))
      (unless prog
        (error 'query
               "no program registered; call (open-session prog) first"))
      (prog 'tells)))

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

  (define (query session name . args)
    (let* ((tells (current-tells))
           (proc (resolve-tell-name name tells)))
      (let-values (((processed binds) (process-args session args)))
        (apply proc session processed)
        (pretty-bindings binds))))

  (define (tell-by-name session name . args)
    (let* ((tells (current-tells))
           (proc (resolve-tell-name name tells)))
      (apply proc session args)))
)
