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
    %unify %unifiable? %nonvar? %chr-error %print %ground?
    %term-variables %compound-to-list %list-to-compound
    %read-term-from-string
    %int-to-float %float-to-int
    %idiv %imod %irem
    %copy-term
    %nil %cons
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
                  '()))

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

  ;;; Numeric conversions. `inexact` is the r6rs replacement for
  ;;; `exact->inexact`; `(exact (truncate x))` truncates toward zero,
  ;;; matching Haskell `truncate :: Double -> Int`.
  (define (%int-to-float n) (inexact n))
  (define (%float-to-int x) (exact (truncate x)))

  ;;; Floor integer division, matching Haskell `div`. r6rs `div` is
  ;;; Euclidean (remainder always non-negative), which disagrees on
  ;;; cases like `20 div -3` where the result must round toward
  ;;; negative infinity.
  (define (%idiv n d) (exact (floor (/ n d))))
  (define (%imod n d) (- n (* (%idiv n d) d)))

  ;;; Truncated remainder, matching Haskell `rem`: the result takes
  ;;; the sign of the dividend. r6rs `mod0` is balanced (result in
  ;;; [-|d|/2, |d|/2)), and the Scheme `remainder` builtin is not
  ;;; visible from `(rnrs)` inside a library in Guile, so we compute
  ;;; it explicitly from `truncate`.
  (define (%irem n d) (- n (* (exact (truncate (/ n d))) d)))

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
