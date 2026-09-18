;;;; Unified runtime for generated CHR programs.
(library (ychr runtime)
  (export
    ;; Session
    make-session session?
    ;; From (ychr var)
    make-var var? var-id deref unify unifiable? equal?/chr
    make-term term? term-functor term-args
    match-term get-arg add-observer! get-var-id
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
    %unify %unifiable? %nonvar? %unbound? %chr-error %chr-inst-error
    chr-inst? %bool-from-value
    %print %write %writeln %ground?
    %term-variables %compound-to-list %list-to-compound
    %name-base
    %read-term-from-string
    %int-to-float %float-to-int
    %add %sub %mul %fdiv
    %lt %gt %le %ge
    %idiv %imod %irem
    %str-concat %str-length %str-upper %str-lower
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
  ;; miss in `evaluables`, and is what lets `X = '+'(1, 1), R is X.`
  ;; evaluate to `2` without the functor having to be qualified.
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
  ;; (`src/YCHR/Internal/Runtime/Registry.hs`) so `X = '+'(1, 1), R is X.`
  ;; works identically on both backends. Each procedure receives the
  ;; session as its first argument (uniform with user-defined
  ;; functions); host calls that don't need it ignore the parameter.
  ;; Keep this list in sync with `baseHostCallRegistry` when adding
  ;; new bare-name host calls.
  (define *prelude-host-calls*
    (let ((t (make-hashtable evaluable-key-hash evaluable-key-eq?)))
      (define (h functor arity proc)
        (hashtable-set! t (make-evaluable-key functor arity) proc))
      ;; Arithmetic — return numeric values
      (h '+ 2 (lambda (s a b) (%add a b)))
      (h '- 2 (lambda (s a b) (%sub a b)))
      (h '* 2 (lambda (s a b) (%mul a b)))
      (h '/ 2 (lambda (s a b) (%fdiv a b)))
      (h 'div 2 (lambda (s a b) (%idiv a b)))
      (h 'mod 2 (lambda (s a b) (%imod a b)))
      (h 'rem 2 (lambda (s a b) (%irem a b)))
      ;; Comparison — return booleans
      (h '< 2 (lambda (s a b) (%lt a b)))
      (h '> 2 (lambda (s a b) (%gt a b)))
      (h '=< 2 (lambda (s a b) (%le a b)))
      (h '>= 2 (lambda (s a b) (%ge a b)))
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
      (h 'string_concat 2 (lambda (s a b) (%str-concat a b)))
      (h 'string_length 1 (lambda (s v) (%str-length v)))
      (h 'string_upper 1 (lambda (s v) (%str-upper v)))
      (h 'string_lower 1 (lambda (s v) (%str-lower v)))
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

  ;;; Is this value an unbound logical variable?
  ;;; Distinct from the prelude's `var/1`, which maps to the raw `var?`
  ;;; record predicate: this one dereferences, matching the Haskell
  ;;; runtime's `__chr_is_unbound`. Generated dispatch code uses it to
  ;;; tell an inconclusive pattern test (the value was not instantiated
  ;;; enough to decide) from a definite mismatch.
  (define (%unbound? v)
    (var? (deref v)))

  ;;; Message bodies reach the reporters below as symbols, because the
  ;;; compiler passes them as `AtomLit`s. Rendering a symbol built from
  ;;; a human sentence prints it escaped (`#{no matching equation \x28;`
  ;;; …), so unwrap to a string first.
  (define (%message->string m)
    (if (symbol? m) (symbol->string m) m))

  ;;; Error
  (define (%chr-error . args)
    (apply error "CHR runtime error" (map %message->string args)))

  ;;; Marker condition carried by every insufficient-instantiation
  ;;; failure. A rule guard compiled with `bsoft-guard` catches exactly
  ;;; this condition and answers #f, so the rule does not fire and is
  ;;; retried when the blocking variable is bound. Everything else
  ;;; propagates.
  (define-condition-type &chr-inst &condition
    make-chr-inst-condition chr-inst?)

  ;;; Raise the same compound condition `error` would build, plus the
  ;;; `&chr-inst` marker, so rendering is unchanged. R6RS `error` is
  ;;; `(error who message irritant ...)`, so `%chr-error`'s
  ;;; `(error "CHR runtime error" detail)` puts the banner in `&who`
  ;;; and the detail in `&message`, with no irritants — mirror that
  ;;; exactly, or instantiation failures would print differently from
  ;;; every other CHR runtime error.
  (define (%raise-chr-inst detail)
    (raise
     (condition
      (make-error)
      (make-chr-inst-condition)
      (make-who-condition "CHR runtime error")
      (make-message-condition detail)
      (make-irritants-condition '()))))

  ;;; Insufficient-instantiation variant of `%chr-error`. Either the
  ;;; whole message body is known at compile time (closure dispatch), or
  ;;; a label plus the runtime-computed 1-based index of the argument
  ;;; that blocked dispatch (0 when unattributable). Mirrors
  ;;; `__chr_inst_error` in the Haskell runtime registry.
  (define %chr-inst-error
    (case-lambda
      ((detail) (%raise-chr-inst (%message->string detail)))
      ((label idx)
       (let* ((name (%message->string label))
              (subject (if (and (integer? idx) (> idx 0))
                           (string-append "argument "
                                          (number->string idx)
                                          " of "
                                          name)
                           name)))
         (%raise-chr-inst
          (string-append
           subject
           " is not sufficiently instantiated to select an equation"
           " (unbound variable at a matched position)"))))))

  ;;; Report a strict primitive's failure, splitting an *instantiation*
  ;;; failure from a general one. Mirrors `argError` in
  ;;; `src/YCHR/Internal/Runtime/Registry.hs`: every caller below is a
  ;;; total function of its arguments' values with no ignored
  ;;; positions, so reaching the failure path with an argument that is
  ;;; still an unbound variable means the value was demanded and was
  ;;; not there. That is what a rule guard catches and turns into a
  ;;; silent `#f`; any other failure (wrong type, division by zero)
  ;;; stays fatal everywhere.
  ;;;
  ;;; The check is on the failure path only, so a correct program never
  ;;; pays for it.
  ;;;
  ;;; Invariant: every caller receives *dereferenced* arguments —
  ;;; `compileHostCallWith` wraps each one in `deref`, and
  ;;; `deep-eval-value` derefs as it walks. `%unbound?` derefs again,
  ;;; so classification is right either way, but a caller that skipped
  ;;; the deref would fail the type test on a *bound* variable and
  ;;; report a general error where the value was there all along.
  (define (%arg-error label args general)
    (if (exists %unbound? args)
        (%chr-inst-error
         (string-append label
                        ": argument is not sufficiently instantiated"
                        " (unbound variable)"))
        (%chr-error general)))

  ;;; The `bfrom-val` bridge: a value expression used in boolean
  ;;; position. Mirrors `boolFromValue` in the Haskell interpreter — an
  ;;; unbound variable here means the guard could not be decided (an
  ;;; instantiation failure, which the enclosing `bsoft-guard` turns
  ;;; into `#f`), while a bound non-boolean is a definite mistake and
  ;;; stays fatal. Scheme truthiness must not decide this: an unbound
  ;;; variable is a record, hence truthy, and would read as *true*.
  (define (%bool-from-value v)
    (let ((d (deref v)))
      (cond
        ((boolean? d) d)
        ((%unbound? d)
         (%chr-inst-error
          "guard is not sufficiently instantiated (unbound variable)"))
        (else (%chr-error "guard did not evaluate to a boolean")))))

  ;;; Arithmetic. Haskell's `numArith2` additionally requires both
  ;;; operands to have the *same* numeric type; Scheme has always
  ;;; accepted mixed exact/inexact here and tightening that is a
  ;;; separate question, so the accept set is left as it was and only
  ;;; the failure path is classified.
  (define (%arith2 op a b)
    (if (and (number? a) (number? b))
        (op a b)
        (%arg-error "arithmetic host call" (list a b)
                    (string-append "arithmetic host call: expected 2"
                                   " numeric arguments of same type, got 2"))))
  (define (%add a b) (%arith2 + a b))
  (define (%sub a b) (%arith2 - a b))
  (define (%mul a b) (%arith2 * a b))
  (define (%fdiv a b)
    (if (and (number? a) (number? b))
        (/ a b)
        (%arg-error "float arithmetic host call" (list a b)
                    (string-append "float arithmetic host call: expected 2"
                                   " Float arguments, got 2"))))

  ;;; Ordering operators. The prelude declares `<`, `>`, `=<` and `>=`
  ;;; over int, float *and* string, so each dispatches on its
  ;;; arguments: two strings compare lexicographically by code point,
  ;;; which is the ordering `string<?` gives and the one Haskell's
  ;;; `compare` on Text gives.
  ;;;
  ;;; Same accept-set caveat as `%arith2`: `ordCmp` requires both
  ;;; operands to have the same type, where this accepts any two
  ;;; numbers, so `1 < 2.0` answers here and is a type error there.
  (define (%cmp2 sop nop a b)
    (cond
      ((and (string? a) (string? b)) (sop a b))
      ((and (number? a) (number? b)) (nop a b))
      (else
       (%arg-error "comparison host call" (list a b)
                   (string-append "comparison host call: expected 2 int,"
                                  " float or string arguments of the same"
                                  " type, got 2")))))
  (define (%lt a b) (%cmp2 string<? < a b))
  (define (%gt a b) (%cmp2 string>? > a b))
  (define (%le a b) (%cmp2 string<=? <= a b))
  (define (%ge a b) (%cmp2 string>=? >= a b))

  ;;; Strings
  (define (%str-concat a b)
    (if (and (string? a) (string? b))
        (string-append a b)
        (%arg-error "string_concat" (list a b)
                    "string_concat: expected 2 Text arguments")))
  (define (%str-length v)
    (if (string? v)
        (string-length v)
        (%arg-error "string_length" (list v)
                    "string_length: expected 1 Text argument")))
  (define (%str-upper v)
    (if (string? v)
        (string-upcase v)
        (%arg-error "string_upper" (list v)
                    "string_upper: expected 1 Text argument")))
  (define (%str-lower v)
    (if (string? v)
        (string-downcase v)
        (%arg-error "string_lower" (list v)
                    "string_lower: expected 1 Text argument")))

  ;;; Print
  (define (%print v) (display v) (newline))

  ;;; Write / writeln. `display` accepts any value, so on its own it
  ;;; has no failure path to classify; `writeStr`/`writeStrLn` in the
  ;;; Haskell registry match `[VText s]` and so reject a bound
  ;;; non-string as well as diagnosing an unbound one. Demanding a
  ;;; string here is what makes the two agree — and what keeps the
  ;;; general message reachable rather than dead. `prelude.chr`
  ;;; declares `write(string)`, so only untyped and `host:` call paths
  ;;; could reach the rejection at all.
  (define (%write v)
    (if (string? v)
        (display v)
        (%arg-error "write" (list v) "write: expected 1 Text argument")))
  (define (%writeln v)
    (if (string? v)
        (begin (display v) (newline))
        (%arg-error "writeln" (list v) "writeln: expected 1 Text argument")))

  ;;; Numeric conversions. `inexact` is the r6rs replacement for
  ;;; `exact->inexact`; `(exact (truncate x))` truncates toward zero,
  ;;; matching Haskell `truncate :: Double -> Int`.
  (define (%int-to-float n)
    (if (number? n)
        (inexact n)
        (%arg-error "int_to_float" (list n)
                    "int_to_float: expected 1 numeric argument")))
  (define (%float-to-int x)
    (if (number? x)
        (exact (truncate x))
        (%arg-error "float_to_int" (list x)
                    "float_to_int: expected 1 numeric argument")))

  ;;; The integer division family. The numeric test comes before the
  ;;; division-by-zero test, because `zero?` on an unbound variable
  ;;; record would raise an untagged wrong-type condition and lose the
  ;;; instantiation diagnosis. Division by zero itself is a *general*
  ;;; error and stays fatal inside a guard, as in `intDivOp2`.
  ;;;
  ;;; The accept set is unchanged and so still wider than Haskell's:
  ;;; `intDivOp2` requires two `VInt`s where this accepts any two
  ;;; numbers, so `5.0 div 2.0` is 2 here and a type error there.
  ;;; Same caveat as `%arith2` — see `SCHEME_BACKEND_GAPS.md`.
  (define (%intdiv2 who op n d)
    (cond
      ((not (and (number? n) (number? d)))
       (%arg-error "integer arithmetic host call" (list n d)
                   (string-append "integer arithmetic host call: expected 2"
                                  " Int arguments, got 2")))
      ((zero? d)
       (%chr-error (string-append "integer " who ": division by zero")))
      (else (op n d))))

  ;;; Floor integer division, matching Haskell `div`. r6rs `div` is
  ;;; Euclidean (remainder always non-negative), which disagrees on
  ;;; cases like `20 div -3` where the result must round toward
  ;;; negative infinity. `mod` is defined from it so the pair stays
  ;;; consistent: the remainder takes the divisor's sign.
  (define (%floor-div n d) (exact (floor (/ n d))))
  (define (%idiv n d) (%intdiv2 "div" %floor-div n d))
  (define (%imod n d)
    (%intdiv2 "mod" (lambda (n d) (- n (* (%floor-div n d) d))) n d))

  ;;; Truncated remainder, matching Haskell `rem`: the result takes
  ;;; the sign of the dividend. r6rs `mod0` is balanced (result in
  ;;; [-|d|/2, |d|/2)), and the Scheme `remainder` builtin is not
  ;;; visible from `(rnrs)` inside a library in Guile, so we compute
  ;;; it explicitly from `truncate`.
  (define (%irem n d)
    (%intdiv2 "rem" (lambda (n d) (- n (* (exact (truncate (/ n d))) d))) n d))

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
  ;;; @prelude__.@ runtime functors. 0-arity compounds collapse to
  ;;; symbols at the runtime layer (matching the Haskell-side @VAtom@
  ;;; canonical form), so %nil is the bare symbol; %cons is a 2-ary
  ;;; term. %nil?/%cons? also accept the legacy 0-ary term form.
  (define (%nil) (string->symbol "prelude__[]"))
  (define (%cons h t) (make-term (string->symbol "prelude__.") (vector h t)))
  (define (%nil? v)
    (or (and (symbol? v) (eq? v (string->symbol "[]")))
        (and (symbol? v) (eq? v (string->symbol "prelude__[]")))
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

  ;;; compound_to_list — also accepts a symbol (the runtime form of a
  ;;; 0-arity compound), returning a singleton list.
  (define (%compound-to-list c)
    (cond
      ((symbol? c) (%cons c (%nil)))
      ((term? c)
       (let ((f (term-functor c)) (a (term-args c)))
         (let loop ((i (- (vector-length a) 1)) (acc (%nil)))
           (if (< i 0) (%cons f acc)
               (loop (- i 1) (%cons (vector-ref a i) acc))))))
      (else
       (%arg-error "compound_to_list" (list c)
                   (string-append "compound_to_list: expected 1 compound"
                                  " or atom argument")))))

  ;;; list_to_compound — a singleton list returns the head symbol
  ;;; directly (matches the 0-arity collapse to 'VAtom).
  ;;; All three rejections mirror `listToCompound` in the Haskell
  ;;; registry, where `fromValueList` returning `Nothing` and the
  ;;; `Just (VAtom f : _)` pattern between them rule out an improper
  ;;; tail, an empty list and a non-atom head. Checking only the
  ;;; length would let `[f, x | T]` build `f(x)` and `[1, 2]` build a
  ;;; term whose functor is a number — the latter escaping as a raw
  ;;; wrong-type condition from the pretty-printer rather than as a
  ;;; CHR error.
  (define (%list-to-compound lst)
    ;; Every rejection is diagnosed against the top-level argument,
    ;; never against the offending sub-part: `argError` is handed the
    ;; host call's argument list, so `[f, x | T]` with `T` unbound is
    ;; a *general* error on both backends — the list itself is bound.
    (define (reject)
      (%arg-error "list_to_compound" (list lst)
                  (string-append "list_to_compound: expected a"
                                 " non-empty list with an atom head")))
    (let loop ((l lst) (acc '()))
      (if (%cons? l)
          (loop (get-arg l 1) (cons (get-arg l 0) acc))
          (let ((parts (reverse acc)))
            (cond
              ((not (%nil? l)) (reject))
              ((null? parts) (reject))
              ((not (symbol? (car parts))) (reject))
              ((null? (cdr parts)) (car parts))
              (else (make-term (car parts) (list->vector (cdr parts)))))))))

  ;;; name_base — the local part of a mangled name symbol. Splits at
  ;;; the first "__", which vmName (Compile/Names.hs) reserves for the
  ;;; module/base separator; a leading "__" (a compiler-internal name
  ;;; like __lambda_3) is not a qualifier, so the whole symbol is the
  ;;; base. Escapes are left in place, exactly as Haskell's
  ;;; baseOfMangled does, so two bases compare equal iff their source
  ;;; spellings do.
  ;;; An unbound argument is an *instantiation* failure, not a type
  ;;; error, so that a rule guard calling `name_base` delays rather than
  ;;; aborting — matching the split `Meta.hs` makes on the Haskell side.
  (define (%name-base v)
    (when (%unbound? v)
      (%chr-inst-error
       "name_base: argument is not sufficiently instantiated (unbound variable)"))
    (unless (symbol? v) (%chr-error "name_base: expected an atom"))
    (let* ((s (symbol->string v))
           (n (string-length s))
           (sep (let loop ((i 0))
                  (cond
                    ((> (+ i 2) n) #f)
                    ((and (char=? (string-ref s i) #\_)
                          (char=? (string-ref s (+ i 1)) #\_))
                     i)
                    (else (loop (+ i 1)))))))
      (if (or (not sep) (zero? sep))
          v
          (string->symbol (substring s (+ sep 2) n)))))

  ;;; read_term_from_string: stub
  (define (%read-term-from-string s)
    (error "%read-term-from-string" "not implemented"))

  ;;; copy_term: deep-copy a term, replacing each unbound variable with
  ;;; a fresh one. Sharing is preserved via an id->fresh-var hashtable,
  ;;; so a term like `f(X, X)` copies to `f(Y, Y)` with the two slots
  ;;; aliased. Mirrors copyTerm in src/YCHR/Internal/Runtime/Registry.hs.
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
            ((term? d)
             (let* ((args (term-args d))
                    (n (vector-length args))
                    (new-args (make-vector n)))
               (do ((i 0 (+ i 1))) ((= i n))
                 (vector-set! new-args i (loop (vector-ref args i))))
               (make-term (term-functor d) new-args)))
            (else d))))))
)
