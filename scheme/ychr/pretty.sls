;;;; Pretty-printer for CHR values.
;;;;
;;;; Matches the output format of prettyTerm in YCHR.Pretty (Haskell).
(library (ychr pretty)
  (export pretty-term)
  (import (rnrs) (ychr var))

  ;; Escape a string for display (matching Haskell renderString).
  (define (escape-string s)
    (let-values (((port extract) (open-string-output-port)))
      (string-for-each
       (lambda (c)
         (cond ((char=? c #\") (put-string port "\\\""))
               ((char=? c #\\) (put-string port "\\\\"))
               ((char=? c #\newline) (put-string port "\\n"))
               ((char=? c #\tab) (put-string port "\\t"))
               (else (put-char port c))))
       s)
      (extract)))

  ;; Recognise both the canonicalized cons functor (@prelude__.@,
  ;; emitted by the renamer-driven pipeline) and the bare @.@ form
  ;; (left in code paths that don't go through the renamer).
  (define (cons-functor? f)
    (or (eq? f (string->symbol "prelude__."))
        (eq? f (string->symbol "."))))

  (define (nil-functor? f)
    (or (eq? f (string->symbol "prelude__[]"))
        (eq? f (string->symbol "[]"))))

  ;; Pretty-print the tail of a Prolog-style list.
  (define (pretty-list-tail v)
    (let ((d (deref v)))
      (cond
        ;; nil: [] (legacy bare-symbol form)
        ((and (symbol? d) (nil-functor? d)) "")
        ;; nil: [] (canonicalized 0-arity term form)
        ((and (term? d)
              (nil-functor? (term-functor d))
              (= (vector-length (term-args d)) 0))
         "")
        ;; cons cell: , head <tail>
        ((and (term? d)
              (cons-functor? (term-functor d))
              (= (vector-length (term-args d)) 2))
         (string-append ", " (pretty-term (get-arg d 0))
                        (pretty-list-tail (get-arg d 1))))
        ;; improper list tail
        (else (string-append "|" (pretty-term d))))))

  ;; Join a list of strings with a separator.
  (define (join sep strs)
    (cond
      ((null? strs) "")
      ((null? (cdr strs)) (car strs))
      (else (string-append (car strs) sep (join sep (cdr strs))))))

  ;; Pretty-print a CHR value, matching Haskell prettyTerm exactly.
  (define (pretty-term v)
    (let ((d (deref v)))
      (cond
        ;; Unbound variable
        ((var? d) "_")
        ;; Wildcard
        ((wildcard? d) "_")
        ;; Boolean (Scheme #t/#f → "true"/"false")
        ((boolean? d) (if d "true" "false"))
        ;; Exact integer. Negative literals are parenthesized to match
        ;; Haskell prettyTerm.
        ((and (integer? d) (exact? d))
         (if (negative? d)
             (string-append "(" (number->string d) ")")
             (number->string d)))
        ;; Inexact number (covers integer-valued floats like 0.0).
        ((and (number? d) (inexact? d))
         (let ((s (number->string d)))
           (if (negative? d)
               (string-append "(" s ")")
               s)))
        ;; String
        ((string? d) (string-append "\"" (escape-string d) "\""))
        ;; Symbol (atom)
        ((symbol? d) (symbol->string d))
        ;; Empty list (canonicalized 0-arity term form)
        ((and (term? d)
              (nil-functor? (term-functor d))
              (= (vector-length (term-args d)) 0))
         "[]")
        ;; Prolog-style list (cons functor arity 2)
        ((and (term? d)
              (cons-functor? (term-functor d))
              (= (vector-length (term-args d)) 2))
         (string-append "[" (pretty-term (get-arg d 0))
                        (pretty-list-tail (get-arg d 1)) "]"))
        ;; Other compound term
        ((term? d)
         (let ((args (vector->list (term-args d))))
           (string-append (symbol->string (term-functor d))
                          "(" (join ", " (map pretty-term args)) ")")))
        ;; Fallback
        (else (call-with-string-output-port
               (lambda (p) (display d p)))))))
)
