;;;; Unified runtime for generated CHR programs.
(library (ychr runtime)
  (export
    ;; Session
    make-session session?
    ;; From (ychr var)
    make-var var? var-id deref unify unifiable? equal?/chr
    make-term term? term-functor term-args
    match-term get-arg add-observer! get-var-id
    *wildcard* wildcard?
    ;; From (ychr store)
    make-store-by-type create-constraint store-constraint
    kill-constraint alive-constraint?
    constraint-id constraint-arg constraint-type
    id-equal? is-constraint-type?
    store-snapshot snapshot-length snapshot-ref
    suspension? suspension-alive? suspension-arg
    suspension-id suspension-type
    ;; From (ychr history)
    add-history! not-in-history?
    ;; From (ychr reactivation)
    enqueue! drain-queue!
    ;; Helpers for generated code
    %unify %unifiable? %nonvar? %chr-error %print %writeln %ground?
    %term-variables %compound-to-list %list-to-compound
    %read-term-from-string
    %int-to-float %float-to-int
    %idiv %imod %irem
    %copy-term
    %nil %cons
    ;; Deep-eval dispatch table for the @is@ operator
    register-evaluable! deep-eval-value
    ;; Session initialization
    %make-session)
  (import (rnrs)
          (ychr session)
          (ychr var)
          (ychr store)
          (ychr history)
          (ychr reactivation)
          (ychr pretty))

  ;;; Session initialization: creates a fully initialized session
  (define (%make-session num-types)
    (make-session 0
                  (make-store-by-type num-types)
                  0
                  (make-hashtable equal-hash equal?)
                  '()
                  '()
                  ;; Deep-eval dispatch table: keys are
                  ;; (functor-symbol . arity) pairs; values are the
                  ;; procedures the deep-evaluator calls when @is@
                  ;; walks a @VTerm@ matching the key. Generated
                  ;; libraries fill this in via @register-evaluable!@.
                  (make-hashtable evaluable-key-hash evaluable-key-eq?)))

  ;;; --- Deep-eval dispatch for the @is@ operator ---

  ;; A key uniquely identifies a (functor, arity) pair. We use a pair
  ;; rather than a record to avoid the boilerplate of declaring a
  ;; record type for every key construction; the contract is
  ;; documented here. The hashtable that uses these keys is built with
  ;; `evaluable-key-hash` and `evaluable-key-eq?` below.
  (define (make-evaluable-key functor arity) (cons functor arity))
  (define (evaluable-key-hash k)
    (+ (* 31 (symbol-hash (car k))) (cdr k)))
  (define (evaluable-key-eq? a b)
    (and (eq? (car a) (car b)) (= (cdr a) (cdr b))))

  ;; Register a procedure to invoke when the deep-evaluator
  ;; encounters a VTerm whose functor and arity match. The procedure
  ;; must accept (session arg1 ... argN) — the same calling
  ;; convention used by generated user-function procedures.
  (define (register-evaluable! s functor arity proc)
    (hashtable-set! (session-evaluables s)
                    (make-evaluable-key functor arity)
                    proc))

  ;; Walk a runtime value, evaluating any compound subterm whose
  ;; (functor, arity) names a registered evaluable. Atomic values
  ;; pass through; bound variables are dereferenced and the
  ;; recursion continues on the dereferenced value. The lookup first
  ;; checks the session's evaluables table (user-defined functions,
  ;; keyed by the fully-qualified VM functor like `prelude__+`), then
  ;; falls back to the prelude host-call table (keyed by the bare
  ;; functor name like `+`). The fallback mirrors the Haskell
  ;; interpreter's `invokeByKey`, which consults `hostCalls` after a
  ;; miss in `evaluables`, and is what lets a user write
  ;; `R is term('+'(1, 1))` without having to qualify the functor.
  ;; A non-evaluable functor raises a runtime error.
  (define (deep-eval-value s v)
    (let ((d (deref v)))
      (cond
        ((term? d)
         (let* ((functor (term-functor d))
                (args (term-args d))
                (n (vector-length args))
                (eval-args (make-vector n)))
           (do ((i 0 (+ i 1))) ((= i n))
             (vector-set! eval-args i
                          (deep-eval-value s (vector-ref args i))))
           (let* ((key (make-evaluable-key functor n))
                  (proc (or (hashtable-ref (session-evaluables s) key #f)
                            (hashtable-ref *prelude-host-calls* key #f))))
             (if proc
                 (apply proc s (vector->list eval-args))
                 ;; Match the Haskell interpreter's message format:
                 ;; "is: functor is not evaluable: <functor>/<arity>"
                 ;; (single concatenated string, no separate detail).
                 (%chr-error
                  (string-append "is: functor is not evaluable: "
                                 (symbol->string functor)
                                 "/"
                                 (number->string n)))))))
        (else d))))

  ;; Prelude host-call fallback table for `deep-eval-value`. Mirrors
  ;; the bare-name entries in Haskell's `baseHostCallRegistry`
  ;; (`src/YCHR/Runtime/Registry.hs`) so `R is term('+'(1, 1))` works
  ;; identically on both backends. Each procedure receives the
  ;; session as its first argument (uniform with user-defined
  ;; functions); host calls that don't need it ignore the parameter.
  ;; Keep this list in sync with `baseHostCallRegistry` when adding
  ;; new bare-name host calls.
  (define *prelude-host-calls*
    (let ((t (make-hashtable evaluable-key-hash evaluable-key-eq?)))
      (define (h functor arity proc)
        (hashtable-set! t (make-evaluable-key functor arity) proc))
      ;; Arithmetic — return numeric values
      (h '+ 2 (lambda (s a b) (+ a b)))
      (h '- 2 (lambda (s a b) (- a b)))
      (h '* 2 (lambda (s a b) (* a b)))
      (h '/ 2 (lambda (s a b) (/ a b)))
      (h 'div 2 (lambda (s a b) (%idiv a b)))
      (h 'mod 2 (lambda (s a b) (%imod a b)))
      (h 'rem 2 (lambda (s a b) (%irem a b)))
      ;; Comparison — return booleans
      (h '< 2 (lambda (s a b) (< a b)))
      (h '> 2 (lambda (s a b) (> a b)))
      (h '=< 2 (lambda (s a b) (<= a b)))
      (h '>= 2 (lambda (s a b) (>= a b)))
      (h '== 2 (lambda (s a b) (equal?/chr a b)))
      ;; Numeric conversions
      (h 'int_to_float 1 (lambda (s n) (%int-to-float n)))
      (h 'float_to_int 1 (lambda (s n) (%float-to-int n)))
      ;; Type predicates
      (h 'float 1 (lambda (s v) (flonum? v)))
      (h 'integer 1 (lambda (s v) (integer? v)))
      (h 'atom 1 (lambda (s v) (symbol? v)))
      (h 'boolean 1 (lambda (s v) (boolean? v)))
      (h 'string 1 (lambda (s v) (string? v)))
      (h 'var 1 (lambda (s v) (var? v)))
      (h 'nonvar 1 (lambda (s v) (%nonvar? v)))
      (h 'unifiable 2 (lambda (s a b) (%unifiable? a b)))
      (h 'ground 1 (lambda (s v) (%ground? v)))
      ;; Strings
      (h 'string_concat 2 (lambda (s a b) (string-append a b)))
      (h 'string_length 1 (lambda (s v) (string-length v)))
      (h 'string_upper 1 (lambda (s v) (string-upcase v)))
      (h 'string_lower 1 (lambda (s v) (string-downcase v)))
      ;; Meta
      (h 'term_variables 1 (lambda (s v) (%term-variables v)))
      (h 'compound_to_list 1 (lambda (s v) (%compound-to-list v)))
      (h 'list_to_compound 1 (lambda (s v) (%list-to-compound v)))
      (h 'copy_term 1 (lambda (s v) (%copy-term s v)))
      t))

  ;;; Unify wrapper: unifies and enqueues observers. Raises a runtime
  ;;; error on failure — YCHR has no backtracking, so a failed
  ;;; unification must abort execution.
  (define (%unify s v1 v2)
    (let-values (((ok observers) (unify v1 v2)))
      (enqueue! s observers)
      (unless ok
        (error '%unify
               (string-append "unification failure: cannot unify "
                              (pretty-term v1)
                              " with "
                              (pretty-term v2))))
      ok))

  ;;; Non-mutating unifiability check
  (define (%unifiable? v1 v2) (unifiable? v1 v2))

  ;;; Type predicates
  (define (%nonvar? v) (not (var? v)))

  ;;; Error
  (define (%chr-error . args) (apply error "CHR runtime error" args))

  ;;; Print
  (define (%print v) (display v) (newline))

  ;;; Writeln (display + newline; `write` itself maps directly to `display`)
  (define (%writeln s) (display s) (newline))

  ;;; Numeric conversions. `inexact` is the r6rs replacement for
  ;;; `exact->inexact`; `(exact (truncate x))` truncates toward zero,
  ;;; matching Haskell `truncate :: Double -> Int`.
  (define (%int-to-float n) (inexact n))
  (define (%float-to-int x) (exact (truncate x)))

  ;;; Floor integer division, matching Haskell `div`. r6rs `div` is
  ;;; Euclidean (remainder always non-negative), which disagrees on
  ;;; cases like `20 div -3` where the result must round toward
  ;;; negative infinity.
  (define (%idiv n d)
    (if (zero? d)
        (error '%idiv "integer div: division by zero")
        (exact (floor (/ n d)))))
  (define (%imod n d)
    (if (zero? d)
        (error '%imod "integer mod: division by zero")
        (- n (* (%idiv n d) d))))

  ;;; Truncated remainder, matching Haskell `rem`: the result takes
  ;;; the sign of the dividend. r6rs `mod0` is balanced (result in
  ;;; [-|d|/2, |d|/2)), and the Scheme `remainder` builtin is not
  ;;; visible from `(rnrs)` inside a library in Guile, so we compute
  ;;; it explicitly from `truncate`.
  (define (%irem n d)
    (if (zero? d)
        (error '%irem "integer rem: division by zero")
        (- n (* (exact (truncate (/ n d))) d))))

  ;;; Groundness check
  (define (%ground? v)
    (let ((d (deref v)))
      (cond ((var? d) #f)
            ((term? d)
             (let ((a (term-args d)))
               (let loop ((i 0))
                 (if (>= i (vector-length a)) #t
                     (and (%ground? (vector-ref a i))
                          (loop (+ i 1)))))))
            (else #t))))

  ;;; Prolog-style list helpers. After the renamer-driven flattening,
  ;;; @[]@ and @.@ are canonicalized to the @prelude__[]@ /
  ;;; @prelude__.@ runtime functors. %nil/%cons construct the canonical
  ;;; form; %nil?/%cons? recognise both the canonical form and the
  ;;; legacy bare form (so values built before renaming still work).
  (define (%nil) (make-term (string->symbol "prelude__[]") (vector)))
  (define (%cons h t) (make-term (string->symbol "prelude__.") (vector h t)))
  (define (%nil? v)
    (or (and (symbol? v) (eq? v (string->symbol "[]")))
        (and (term? v)
             (eq? (term-functor v) (string->symbol "prelude__[]"))
             (= (vector-length (term-args v)) 0))))
  (define (%cons? v)
    (and (term? v)
         (or (eq? (term-functor v) (string->symbol "prelude__."))
             (eq? (term-functor v) (string->symbol ".")))
         (= (vector-length (term-args v)) 2)))

  ;;; term_variables
  (define (%term-variables t)
    (let ((seen '()) (result '()))
      (define (walk v)
        (let ((d (deref v)))
          (cond ((var? d)
                 (let ((id (var-id d)))
                   (unless (memv id seen)
                     (set! seen (cons id seen))
                     (set! result (cons d result)))))
                ((term? d)
                 (let ((a (term-args d)))
                   (do ((i 0 (+ i 1))) ((= i (vector-length a)))
                     (walk (vector-ref a i))))))))
      (walk t)
      (fold-right %cons (%nil) (reverse result))))

  ;;; compound_to_list
  (define (%compound-to-list c)
    (let ((f (term-functor c)) (a (term-args c)))
      (let loop ((i (- (vector-length a) 1)) (acc (%nil)))
        (if (< i 0) (%cons f acc)
            (loop (- i 1) (%cons (vector-ref a i) acc))))))

  ;;; list_to_compound
  (define (%list-to-compound lst)
    (let loop ((l lst) (acc '()))
      (if (%cons? l)
          (loop (get-arg l 1) (cons (get-arg l 0) acc))
          (let ((parts (reverse acc)))
            (make-term (car parts) (list->vector (cdr parts)))))))

  ;;; read_term_from_string: stub
  (define (%read-term-from-string s)
    (error "%read-term-from-string" "not implemented"))

  ;;; copy_term: deep-copy a term, replacing each unbound variable with
  ;;; a fresh one. Sharing is preserved via an id->fresh-var hashtable,
  ;;; so a term like `f(X, X)` copies to `f(Y, Y)` with the two slots
  ;;; aliased. Mirrors copyTerm in src/YCHR/Runtime/Registry.hs.
  (define (%copy-term s v)
    (let ((cache (make-eqv-hashtable)))
      (let loop ((v v))
        (let ((d (deref v)))
          (cond
            ((var? d)
             (let* ((id (var-id d))
                    (cached (hashtable-ref cache id #f)))
               (or cached
                   (let ((fresh (make-var s)))
                     (hashtable-set! cache id fresh)
                     fresh))))
            ((wildcard? d) (make-var s))
            ((term? d)
             (let* ((args (term-args d))
                    (n (vector-length args))
                    (new-args (make-vector n)))
               (do ((i 0 (+ i 1))) ((= i n))
                 (vector-set! new-args i (loop (vector-ref args i))))
               (make-term (term-functor d) new-args)))
            (else d))))))
)
