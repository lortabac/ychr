;;;; Pretty-printer for CHR values.
;;;;
;;;; Matches the output format of prettyTerm in YCHR.Pretty (Haskell).
(library (ychr pretty)
  (export pretty-term pretty-bindings bindings->string)
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

  ;; True if CH is an ASCII hex digit (0-9, a-f).
  ;; encodeText in Compile/Names.hs uses lowercase hex.
  (define (hex-digit? ch)
    (or (and (char<=? #\0 ch) (char<=? ch #\9))
        (and (char<=? #\a ch) (char<=? ch #\f))))

  ;; True if S starting at I has six consecutive hex digits.
  (define (six-hex? s i)
    (and (<= (+ i 6) (string-length s))
         (hex-digit? (string-ref s i))
         (hex-digit? (string-ref s (+ i 1)))
         (hex-digit? (string-ref s (+ i 2)))
         (hex-digit? (string-ref s (+ i 3)))
         (hex-digit? (string-ref s (+ i 4)))
         (hex-digit? (string-ref s (+ i 5)))))

  ;; Replace each "%%u<6 hex digits>" escape in S between [FROM, TO)
  ;; with its character. Inverse of encodeText in Compile/Names.hs:
  ;; the encoder emits exactly six lowercase hex digits per escape
  ;; with no closing delimiter, so the decoder consumes the same.
  (define (decode-escapes-range s from to)
    (let-values (((port extract) (open-string-output-port)))
      (let loop ((i from))
        (cond
          ((>= i to) (extract))
          ((and (<= (+ i 9) to)
                (char=? (string-ref s i) #\%)
                (char=? (string-ref s (+ i 1)) #\%)
                (char=? (string-ref s (+ i 2)) #\u)
                (six-hex? s (+ i 3)))
           (let* ((hex (substring s (+ i 3) (+ i 9)))
                  (code (string->number hex 16)))
             ;; Reject surrogates and out-of-range code points
             ;; (encodeText never emits these) so a malformed input
             ;; doesn't crash integer->char.
             (if (and (<= code #x10FFFF)
                      (not (and (>= code #xD800) (<= code #xDFFF))))
                 (begin (put-char port (integer->char code))
                        (loop (+ i 9)))
                 (begin (put-char port (string-ref s i))
                        (loop (+ i 1))))))
          (else
           (put-char port (string-ref s i))
           (loop (+ i 1)))))))

  (define (decode-escapes s)
    (decode-escapes-range s 0 (string-length s)))

  ;; Find the first occurrence of "__" in S, or #f if absent.
  (define (find-double-underscore s)
    (let ((n (string-length s)))
      (let loop ((i 0))
        (cond
          ((> (+ i 2) n) #f)
          ((and (char=? (string-ref s i) #\_)
                (char=? (string-ref s (+ i 1)) #\_))
           i)
          (else (loop (+ i 1)))))))

  ;; Inverse of vmName in Compile/Names.hs. The encoding is injective
  ;; (see encodeText's haddock): encodeText emits no "__" of its own
  ;; (non-ASCII chars use "%%u<6 hex>" instead), and the lexer rejects
  ;; "__" in source, so the only "__" in the mangled form is the
  ;; module/base separator. Split there; decode "%%u..." escapes in
  ;; each half. A leading "__" (compiler-internal name like
  ;; "__lambda_3") yields an empty module — treat as unqualified.
  (define (unmangle-qualified s)
    (let ((n (string-length s))
          (sep (find-double-underscore s)))
      (cond
        ((or (not sep) (zero? sep)) (decode-escapes s))
        (else
         (string-append (decode-escapes-range s 0 sep)
                        ":"
                        (decode-escapes-range s (+ sep 2) n))))))

  (define (pretty-symbol sym)
    (unmangle-qualified (symbol->string sym)))

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
        ;; Empty list (atom form — the runtime collapse of 0-arity
        ;; @prelude:[]@). Checked before the general symbol case so the
        ;; nil functor isn't unmangled to "prelude:[]".
        ((and (symbol? d) (nil-functor? d)) "[]")
        ;; Symbol (atom)
        ((symbol? d) (pretty-symbol d))
        ;; Empty list (legacy 0-arity term form)
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
           (string-append (pretty-symbol (term-functor d))
                          "(" (join ", " (map pretty-term args)) ")")))
        ;; Fallback
        (else (call-with-string-output-port
               (lambda (p) (display d p)))))))

  ;; Format an alist of ((symbol . value) ...) bindings as
  ;;   Name = pretty-term\n
  ;; one per line, sorted by symbol name. Matches the output of
  ;; YCHR.Pretty.prettyBindings on the Haskell side. Returns a string.
  (define (bindings->string bs)
    (let ((sorted (list-sort
                   (lambda (a b)
                     (string<? (symbol->string (car a))
                               (symbol->string (car b))))
                   bs)))
      (let-values (((port extract) (open-string-output-port)))
        (for-each
         (lambda (b)
           (put-string port (symbol->string (car b)))
           (put-string port " = ")
           (put-string port (pretty-term (cdr b)))
           (put-char port #\newline))
         sorted)
        (extract))))

  ;; Print bindings using `bindings->string`. Side-effect-only wrapper
  ;; for the common case where the formatted output is just displayed.
  (define (pretty-bindings bs)
    (display (bindings->string bs)))
)
