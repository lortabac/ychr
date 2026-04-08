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

  ;; Pretty-print the tail of a Prolog-style list.
  (define (pretty-list-tail v)
    (let ((d (deref v)))
      (cond
        ;; nil: []
        ((and (symbol? d) (string=? (symbol->string d) "[]")) "")
        ;; cons cell: , head <tail>
        ((and (term? d)
              (eq? (term-functor d) (string->symbol "."))
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
        ;; Integer
        ((integer? d) (number->string d))
        ;; String
        ((string? d) (string-append "\"" (escape-string d) "\""))
        ;; Symbol (atom)
        ((symbol? d) (symbol->string d))
        ;; Prolog-style list (functor "." arity 2)
        ((and (term? d)
              (eq? (term-functor d) (string->symbol "."))
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
