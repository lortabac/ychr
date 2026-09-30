(import (rnrs)
        (srfi :64)
        (ychr runtime)
        (ychr pretty))

(define (fresh-session) (%make-session 0))

(test-begin "runtime")

;;; --------------------------------------------------------------------------
;;; %unify success cases
;;; --------------------------------------------------------------------------

(test-group "%unify success"
  (test-assert "atom = atom"
               (%unify (fresh-session) 'a 'a))
  (test-assert "int = int"
               (%unify (fresh-session) 1 1))
  (let* ((s (fresh-session))
         (x (make-var s)))
    (test-assert "var = int" (%unify s x 1))))

;;; --------------------------------------------------------------------------
;;; %unify failure raises a runtime error
;;; --------------------------------------------------------------------------

(test-group "%unify failure raises"
  (test-error "int mismatch"
              (%unify (fresh-session) 1 2))
  (test-error "atom mismatch"
              (%unify (fresh-session) 'foo 'bar))
  (test-error "list length mismatch"
              (let* ((s (fresh-session))
                     (x (make-var s))
                     (y (make-var s))
                     (lhs (%cons x (%cons y (%nil))))
                     (rhs (%cons 1 (%cons 2 (%cons 3 (%nil))))))
                (%unify s lhs rhs))))

;;; --------------------------------------------------------------------------
;;; Strict primitives classify their failures
;;;
;;; A rule guard is compiled to `(guard (%c ((chr-inst? %c) #f)) ...)`, so a
;;; primitive that fails because an argument is still unbound must raise a
;;; condition satisfying `chr-inst?` — that is what makes the rule delay and
;;; be retried after reactivation instead of aborting the query. A primitive
;;; that fails on a *bound* argument of the wrong type is a definite mistake
;;; and must not carry the marker, so it stays fatal inside a guard too.
;;;
;;; This mirrors `argError` in src/YCHR/Internal/Runtime/Registry.hs. See
;;; §"Soft guard failure" in docs/reference/language.md.
;;; --------------------------------------------------------------------------

;;; Run `thunk` and report how it failed: 'inst, 'general, or 'no-error.
(define (failure-kind thunk)
  (guard (c ((chr-inst? c) 'inst)
            (#t 'general))
    (thunk)
    'no-error))

(define (fresh-var) (make-var (fresh-session)))

;;; Each entry is (name unbound-call bound-wrong-type-call).
(define strict-primitives
  (list
   (list "+"              (lambda () (%add (fresh-var) 1))
                          (lambda () (%add 'a 1)))
   (list "-"              (lambda () (%sub 1 (fresh-var)))
                          (lambda () (%sub 1 'a)))
   (list "*"              (lambda () (%mul (fresh-var) 2))
                          (lambda () (%mul "x" 2)))
   (list "/"              (lambda () (%fdiv (fresh-var) 2))
                          (lambda () (%fdiv 'a 2)))
   (list "div"            (lambda () (%idiv (fresh-var) 2))
                          (lambda () (%idiv 'a 2)))
   (list "mod"            (lambda () (%imod 1 (fresh-var)))
                          (lambda () (%imod 1 'a)))
   (list "rem"            (lambda () (%irem (fresh-var) 2))
                          (lambda () (%irem "x" 2)))
   (list "<"              (lambda () (%lt (fresh-var) 1))
                          (lambda () (%lt 'a 1)))
   (list ">"              (lambda () (%gt (fresh-var) 1))
                          (lambda () (%gt "x" 1)))
   (list "=<"             (lambda () (%le 1 (fresh-var)))
                          (lambda () (%le 1 'a)))
   (list ">="             (lambda () (%ge 1 (fresh-var)))
                          (lambda () (%ge 1 'a)))
   (list "int_to_float"   (lambda () (%int-to-float (fresh-var)))
                          (lambda () (%int-to-float 'a)))
   (list "float_to_int"   (lambda () (%float-to-int (fresh-var)))
                          (lambda () (%float-to-int 'a)))
   (list "string_concat"  (lambda () (%str-concat (fresh-var) "b"))
                          (lambda () (%str-concat 1 "b")))
   (list "string_length"  (lambda () (%str-length (fresh-var)))
                          (lambda () (%str-length 1)))
   (list "string_upper"   (lambda () (%str-upper (fresh-var)))
                          (lambda () (%str-upper 1)))
   (list "string_lower"   (lambda () (%str-lower (fresh-var)))
                          (lambda () (%str-lower 1)))
   (list "write"          (lambda () (%write (fresh-var)))
                          (lambda () (%write 1)))
   (list "writeln"        (lambda () (%writeln (fresh-var)))
                          (lambda () (%writeln 1)))
   (list "compound_to_list"
                          (lambda () (%compound-to-list (fresh-var)))
                          (lambda () (%compound-to-list 1)))
   (list "list_to_compound"
                          (lambda () (%list-to-compound (fresh-var)))
                          (lambda () (%list-to-compound 1)))
   (list "name_base"      (lambda () (%name-base (fresh-var)))
                          (lambda () (%name-base 1)))))

(test-group "unbound argument is an instantiation failure"
  (for-each
   (lambda (entry)
     (test-equal (car entry) 'inst (failure-kind (cadr entry))))
   strict-primitives))

(test-group "bound wrong-typed argument is a general failure"
  (for-each
   (lambda (entry)
     (when (caddr entry)
       (test-equal (car entry) 'general (failure-kind (caddr entry)))))
   strict-primitives))

;;; language.md §Soft guard failure: "When a call is both
;;; under-instantiated and ill-typed ... the instantiation diagnosis
;;; wins." In a guard that means the rule delays; once the variable is
;;; bound, the type error surfaces as a hard general failure.
(test-group "instantiation outranks a type error"
  (test-equal "unbound + ill-typed" 'inst
              (failure-kind (lambda () (%add (fresh-var) "foo"))))
  (test-equal "same call once bound" 'general
              (failure-kind (lambda () (%add 1 "foo")))))

;;; Division by zero is a definite mistake, not a missing binding, so it
;;; must abort a guard rather than delay it.
(test-group "division by zero stays a general failure"
  (test-equal "div" 'general (failure-kind (lambda () (%idiv 1 0))))
  (test-equal "mod" 'general (failure-kind (lambda () (%imod 1 0))))
  (test-equal "rem" 'general (failure-kind (lambda () (%irem 1 0)))))

;;; `%intdiv2` tests numeric-ness *before* division by zero on purpose:
;;; `zero?` on a variable record raises an untagged wrong-type
;;; condition, which would abort a guard that should have delayed.
;;; Swapping the two `cond` clauses turns these from 'inst to 'general.
(test-group "unbound divisor outranks division by zero"
  (test-equal "div" 'inst (failure-kind (lambda () (%idiv (fresh-var) 0))))
  (test-equal "mod" 'inst (failure-kind (lambda () (%imod (fresh-var) 0))))
  (test-equal "rem" 'inst (failure-kind (lambda () (%irem (fresh-var) 0)))))

;;; The other half of the language.md table: primitives that are total
;;; on unbound values must answer normally and never raise. Wrapping
;;; one of these by mistake would turn a working guard into one that
;;; silently delays for ever.
(test-group "total primitives never raise on an unbound argument"
  (test-equal "==" #f (equal?/chr (fresh-var) 1))
  (test-assert "unifiable" (%unifiable? (fresh-var) 1))
  (test-equal "ground" #f (%ground? (fresh-var)))
  (test-assert "var" (var? (fresh-var)))
  (test-equal "nonvar" #f (%nonvar? (fresh-var)))
  (test-equal "integer" #f (integer? (fresh-var)))
  (test-equal "string" #f (string? (fresh-var)))
  (let* ((s (fresh-session))
         (x (make-var s)))
    (test-assert "term_variables" (eq? x (get-arg (%term-variables x) 0)))
    (test-assert "copy_term" (var? (%copy-term s x)))))

;;; The happy paths must be untouched by the classification wrappers.
(test-group "strict primitives still compute"
  (test-equal "+" 3 (%add 1 2))
  (test-equal "-" 1 (%sub 3 2))
  (test-equal "*" 6 (%mul 2 3))
  (test-equal "/" 2.5 (%fdiv 5.0 2.0))
  (test-equal "div rounds toward negative infinity" -7 (%idiv 20 -3))
  (test-equal "mod takes the divisor's sign" -1 (%imod 20 -3))
  (test-equal "rem takes the dividend's sign" 2 (%irem 20 -3))
  (test-assert "< on ints" (%lt 1 2))
  (test-assert "< on strings" (%lt "a" "b"))
  (test-assert ">= on floats" (%ge 2.5 2.5))
  (test-equal "int_to_float" 1.0 (%int-to-float 1))
  (test-equal "float_to_int truncates toward zero" -1 (%float-to-int -1.7))
  (test-equal "string_concat" "ab" (%str-concat "a" "b"))
  (test-equal "string_length" 3 (%str-length "abc"))
  (test-equal "string_upper" "AB" (%str-upper "ab"))
  (test-equal "string_lower" "ab" (%str-lower "AB")))

;;; `listToCompound` in the Haskell registry rejects an improper tail, an
;;; empty list and a non-atom head. Checking only the length would let
;;; `[f, x | T]` quietly build `f(x)` and `[1, 2]` build a term whose
;;; functor is a number. Every rejection is diagnosed against the
;;; top-level argument, so a bound list with an unbound tail is a
;;; *general* failure — `argError` sees the list, and the list is bound.
(test-group "%list-to-compound rejections"
  (test-equal "well-formed" 'f
              (term-functor (%list-to-compound
                             (%cons 'f (%cons 1 (%nil))))))
  (test-equal "improper tail" 'general
              (failure-kind (lambda ()
                              (%list-to-compound
                               (%cons 'f (%cons 1 (fresh-var)))))))
  (test-equal "non-atom head" 'general
              (failure-kind (lambda ()
                              (%list-to-compound
                               (%cons 1 (%cons 2 (%nil)))))))
  (test-equal "empty list" 'general
              (failure-kind (lambda () (%list-to-compound (%nil)))))
  (test-equal "unbound argument" 'inst
              (failure-kind (lambda () (%list-to-compound (fresh-var))))))

;;; --------------------------------------------------------------------------
;;; %bool-from-value — the `bfrom-val` bridge
;;;
;;; Scheme truthiness must not decide a guard: an unbound variable is a
;;; record, hence truthy, and would read as *true* rather than as "cannot
;;; be decided yet". Mirrors `boolFromValue` in the Haskell interpreter.
;;; --------------------------------------------------------------------------

(test-group "%bool-from-value"
  (test-assert "true passes through" (%bool-from-value #t))
  (test-equal "false passes through" #f (%bool-from-value #f))
  (test-equal "unbound variable is an instantiation failure"
              'inst
              (failure-kind (lambda () (%bool-from-value (fresh-var)))))
  (test-equal "bound non-boolean is a general failure"
              'general
              (failure-kind (lambda () (%bool-from-value 5))))
  (let* ((s (fresh-session))
         (x (make-var s)))
    (%unify s x #t)
    (test-assert "derefs through a binding" (%bool-from-value x))))

;;; --------------------------------------------------------------------------
;;; %apply-closure — the `'$call'` dispatch construct
;;;
;;; Mirrors `applyClosure` in the Haskell interpreter. A closure resolves
;;; through the session's callables table by (functor, identity, declared
;;; arity); a function reference is looked up at the arity it records, a
;;; lifted lambda at the arity it is applied at, captured values are
;;; passed before the application arguments, an unbound closure is an
;;; instantiation failure, and everything else is a definite mismatch.
;;;
;;; The identities are built with `string->symbol` because a flattened
;;; function name contains `:`, which R6RS does not admit as a subsequent
;;; identifier character even though Guile reads it.
;;; --------------------------------------------------------------------------

(define prelude-double (string->symbol "prelude:double"))
(define prelude-nope (string->symbol "prelude:nope"))

;; A session with three callables registered: a function reference at
;; two arities (so a key of functor and identity alone would resolve the
;; unary reference to the binary procedure — the declared-arity check is
;; what stops it) and a unary lifted lambda carrying one capture.
(define (closure-session)
  (let ((s (fresh-session)))
    (register-callable! s '/ prelude-double 1 (lambda (s a) (* 2 a)))
    (register-callable! s '/ prelude-double 2 (lambda (s a b) (+ a b)))
    (register-callable! s '__closure 'm__lambda_0 1 (lambda (s cap a) (+ cap a)))
    s))

;; The closure value a `fun name/arity` reference produces.
(define (funref-closure identity arity)
  (make-term '/ (vector identity arity)))

;;; --------------------------------------------------------------------------
;;; `deep-eval-value` dispatch for `host:` terms
;;;
;;; A `host:` call in data position keeps the vmName `host__F` as its
;;; functor, while `*prelude-host-calls*` is keyed by the bare name `F`.
;;; The walker decodes the functor before the host-call fallback and
;;; reports the decoded name in its diagnostic, mirroring the Haskell
;;; interpreter's `invokeByKey`. Pinned here because the golden harness
;;; runs positive cases only, and because the arity-mismatch diagnostic
;;; differs between the backends (see dev-docs/SCHEME_BACKEND_GAPS.md).
;;; --------------------------------------------------------------------------

;; The message carried by the runtime error `thunk` raises, or #f when
;; it returns normally.
(define (error-message thunk)
  (guard (c ((error? c) (condition-message c)))
    (thunk)
    #f))

;; The unit atom both `%write` and `%writeln` return, Haskell's
;; `VAtom "()"`.
(define unit-atom (string->symbol "()"))

;; Capture everything `thunk` writes to (current-output-port) and
;; return it as a string. The only way to assert a printed form.
(define (capture-stdout thunk)
  (cdr (capture-stdout+value thunk)))

;; Capture both the value `thunk` returns and what it printed, as
;; (value . text). Used where a call both prints and yields a value.
(define (capture-stdout+value thunk)
  (let-values (((port extract) (open-string-output-port)))
    (let ((v (parameterize ((current-output-port port)) (thunk))))
      (cons v (extract)))))

(test-group "host functor deep-eval"
  (test-equal "host__+/2 evaluates"
              2
              (deep-eval-value (fresh-session)
                               (make-term 'host__+ (vector 1 1))))
  (test-equal "a nested host call evaluates"
              7
              (deep-eval-value (fresh-session)
                               (make-term 'host__+
                                          (vector (make-term 'host__*
                                                             (vector 2 3))
                                                  1))))
  ;; Arity is part of the prelude key, so the unary shape misses even
  ;; though `-` is registered at arity 2; Haskell reaches the binary
  ;; primitive instead (the recorded divergence).
  (test-equal "an arity no primitive provides is not evaluable"
              "is: functor is not evaluable: host:-/1"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'host__- (vector 3))))))
  ;; The message names the decoded functor, not the vmName.
  (test-equal "a non-evaluable functor is named in decoded form"
              "is: functor is not evaluable: m:pair/2"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'm__pair (vector 1 2))))))
  (test-equal "an undeclared functor is named as-is"
              "is: functor is not evaluable: pair/2"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'pair (vector 1 2))))))
  ;; The raw-functor tier: a bare host name that the compiler never
  ;; canonicalized (a `quote`d atom, say) is answered directly.
  (test-equal "a bare host name evaluates"
              1
              (deep-eval-value (fresh-session)
                               (make-term 'copy_term (vector 1))))
  ;; Arity is part of the prelude key, so the wrong arity misses the
  ;; table and is reported as not-evaluable. Haskell's name-only
  ;; registry reaches the primitive and reports *its* arity error
  ;; instead — the same divergence as `host:'-'(3)`, recorded in
  ;; dev-docs/SCHEME_BACKEND_GAPS.md.
  (test-equal "a bare host name at a wrong arity is not evaluable"
              "is: functor is not evaluable: copy_term/2"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'copy_term (vector 1 2))))))
  ;; The `host:` shape is matched on the raw vmName `host__F`, never on
  ;; a decoded `host:` prefix, so an unqualified atom is not promoted
  ;; to a host call by spelling alone: `host__no_such` starts with the
  ;; `host__` text but carries no module split, and decodes to the
  ;; unqualified `host:no_such`.
  (test-equal "an unqualified host-looking name is not a host call"
              "is: functor is not evaluable: host:no_such/1"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'host__no_such (vector "x"))))))
  ;; `write`/`writeln` print and then yield the unit atom, as the
  ;; Haskell registry's `writeStr`/`writeStrLn` do.
  (test-equal "host__write prints and returns unit"
              unit-atom
              (deep-eval-value (fresh-session)
                               (make-term 'host__write (vector "x"))))
  (test-equal "host__writeln prints and returns unit"
              unit-atom
              (deep-eval-value (fresh-session)
                               (make-term 'host__writeln (vector "x"))))
  ;; `print` lives in Haskell's `metaHostCallRegistry`, which the
  ;; composed `defaultHostCallRegistry` includes, so `is` reaches it;
  ;; the Scheme table registered it at arity 1. Pinned as (value .
  ;; stdout) so the printed form is checked too.
  (test-equal "host__print deep-evaluates to unit"
              (cons unit-atom "1\n")
              (capture-stdout+value
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'host__print (vector 1))))))
  ;; The raw-functor tier answers a bare `print` atom too.
  (test-equal "a bare print name deep-evaluates to unit"
              (cons unit-atom "1\n")
              (capture-stdout+value
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'print (vector 1)))))))

;;; --------------------------------------------------------------------------
;;; `%print`: the runtime's `print` host call
;;;
;;; Mirrors `print` in `YCHR.Internal.Meta`: each argument is rendered
;;; with the surface pretty-printer (`prettyTerm` on the Haskell side)
;;; on its own line, and the unit atom is returned. Pinned here because
;;; `print` writes to stdout, which the golden harness compares on the
;;; Scheme side but ignores on the Haskell side, so no shared
;;; `.expected` can capture it.
;;; --------------------------------------------------------------------------

(test-group "%print pretty-prints and returns unit"
  (test-equal "compound with an unbound variable"
              "pair(1, _)\n"
              (capture-stdout
               (lambda ()
                 (%print (make-term 'pair (vector 1 (fresh-var)))))))
  (test-equal "string is quoted"
              "\"hi\"\n"
              (capture-stdout (lambda () (%print "hi"))))
  (test-equal "list uses surface syntax"
              "[1, 2]\n"
              (capture-stdout
               (lambda () (%print (%cons 1 (%cons 2 (%nil)))))))
  (test-equal "atom stays bare"
              "foo\n"
              (capture-stdout (lambda () (%print 'foo))))
  ;; Negative integers are parenthesized and booleans become
  ;; `true`/`false`; both differ from `display`, so these two bite if
  ;; `%print` ever regresses to a raw `display`.
  (test-equal "negative integer is parenthesized"
              "(-3)\n"
              (capture-stdout (lambda () (%print -3))))
  (test-equal "boolean uses surface spelling"
              "true\n"
              (capture-stdout (lambda () (%print #t))))
  (test-equal "one line per argument"
              "1\n\"hi\"\n"
              (capture-stdout (lambda () (%print 1 "hi"))))
  (test-equal "no arguments prints nothing and returns unit"
              (cons unit-atom "")
              (capture-stdout+value (lambda () (%print))))
  (test-equal "returns the unit atom"
              (cons unit-atom "42\n")
              (capture-stdout+value (lambda () (%print 42)))))

;;; --------------------------------------------------------------------------
;;; `pretty-term` quotes atoms like Haskell's `renderAtom`
;;;
;;; `prettyTerm` renders an atom through `renderAtom`/`needsQuoting`
;;; (YCHR.Internal.Pretty / YCHR.Internal.PExpr): only a bare lowercase
;;; identifier of letters, digits and underscores stays bare, and the
;;; module and base halves of a qualified name are quoted independently.
;;; Locked here against the printer itself so a regression is local, and
;;; because `a²`/`aⅧ` (categories No/Nl) would silently become quoted
;;; under a narrower `char-alphabetic?`/`char-numeric?` port.
;;; --------------------------------------------------------------------------

(test-group "pretty-term quotes atoms like renderAtom"
  (test-equal "bare lowercase atom"
              "foo"
              (pretty-term 'foo))
  (test-equal "underscore stays bare"
              "foo_bar"
              (pretty-term 'foo_bar))
  (test-equal "the unit atom is quoted"
              "'()'"
              (pretty-term unit-atom))
  (test-equal "a space is quoted"
              "'hello world'"
              (pretty-term (string->symbol "hello world")))
  (test-equal "a word operator is quoted"
              "'is'"
              (pretty-term 'is))
  (test-equal "an uppercase lead is quoted"
              "'Abc'"
              (pretty-term (string->symbol "Abc")))
  (test-equal "an embedded quote is doubled"
              "'a''b'"
              (pretty-term (string->symbol "a'b")))
  ;; Nl/No categories are isAlphaNum in Haskell: they must stay bare,
  ;; which is why the predicate uses `char-general-category`.
  (test-equal "an No character stays bare"
              "a²"
              (pretty-term (string->symbol "a²")))
  (test-equal "an Nl character stays bare"
              "aⅧ"
              (pretty-term (string->symbol "aⅧ")))
  ;; Lt (titlecase) is isAlpha but not isLower: quoted as a lead,
  ;; allowed in the tail.
  (test-equal "a titlecase lead is quoted"
              "'ǅabc'"
              (pretty-term (string->symbol "ǅabc")))
  (test-equal "a titlecase tail character stays bare"
              "aǅb"
              (pretty-term (string->symbol "aǅb")))
  (test-equal "qualified halves are quoted independently"
              "mymodule:'£foo'"
              (pretty-term (string->symbol "mymodule__%%u0000a3foo")))
  (test-equal "qualified bare halves stay bare"
              "mymodule:uaafoo"
              (pretty-term (string->symbol "mymodule__uaafoo"))))

;;; --------------------------------------------------------------------------
;;; Unimplemented meta host calls are bound stubs
;;;
;;; A generated library defines every function of an imported library,
;;; so these names are referenced even by a program that uses none of
;;; them. They must be *bound* (a bare unbound identifier makes the
;;; whole module fail to load on a strict R6RS implementation such as
;;; Chez); the gap is reported only when the function is called.
;;; --------------------------------------------------------------------------

(test-group "unimplemented meta host calls raise on call"
  (test-equal "read_term_from_string bound and raises"
              "not implemented"
              (error-message (lambda () (%read-term-from-string "x"))))
  (test-equal "print_store bound and raises"
              "not implemented"
              (error-message (lambda () (%print-store))))
  (test-equal "write_term_to_string bound and raises"
              "not implemented"
              (error-message (lambda () (%write-term-to-string 1))))
  (test-equal "write_store_to_list bound and raises"
              "not implemented"
              (error-message (lambda () (%write-store-to-list))))
  (test-equal "run_chr_session bound and raises"
              "not implemented"
              (error-message (lambda () (%run-chr-session 1)))))

;;; --------------------------------------------------------------------------
;;; `deep-eval-value` arguments: declared calls evaluate, data stays data
;;;
;;; An argument is dispatched only when its own functor is evaluable.
;;; Before the split, the walker dispatched arguments before checking
;;; the outer functor, so a list argument to a declared call stopped at
;;; the cons cell. The data walk still dereferences variables, so the
;;; data carries current bindings.
;;; --------------------------------------------------------------------------

;; A session with one unary identity function registered, so a compound
;; can be passed through a declared call unchanged.
(define (identity-session)
  (let ((s (fresh-session)))
    (register-evaluable! s 'user__id 1 (lambda (s a) a))
    s))

(test-group "host functor deep-eval arguments"
  ;; The list argument is a constructor term, so it stays data; the
  ;; answer is the term itself, not an error about `prelude__.`.
  (test-assert "a constructor argument stays data"
               (term? (deep-eval-value
                       (identity-session)
                       (make-term 'user__id
                                  (vector (%cons 1 (%cons 2 (%nil))))))))
  ;; A registered call in argument position is evaluated. `host__+`
  ;; rather than `prelude__+`: the latter's evaluables entry is
  ;; registered by a generated program, which `fresh-session` does not
  ;; build, while the prelude host-call table is always present.
  (test-equal "a declared call argument is evaluated"
              2
              (deep-eval-value (identity-session)
                               (make-term 'user__id
                                          (vector (make-term 'host__+
                                                             (vector 1 1))))))
  ;; A bound variable inside a data argument is dereferenced, but what
  ;; it is bound to is not dispatched.
  (let* ((s (identity-session))
         (x (make-var s)))
    (%unify s x 7)
    (test-equal "a variable inside a data argument is dereferenced"
                7
                (get-arg (deep-eval-value
                          s
                          (make-term 'user__id
                                     (vector (make-term 'pair (vector x 2)))))
                         0)))
  ;; The outermost compound is still required to be evaluable.
  (test-equal "an outer constructor is still a not-evaluable error"
              "is: functor is not evaluable: pair/2"
              (error-message
               (lambda ()
                 (deep-eval-value (fresh-session)
                                  (make-term 'pair (vector 1 2)))))))

;;; --------------------------------------------------------------------------
;;; `%apply-closure`
;;; --------------------------------------------------------------------------

(test-group "%apply-closure"
  (test-equal "function reference dispatches"
              10
              (%apply-closure (closure-session)
                              (funref-closure prelude-double 1)
                              5))
  (test-equal "arity mismatch is a general failure"
              'general
              (failure-kind
               (lambda ()
                 (%apply-closure (closure-session)
                                 (funref-closure prelude-double 1)
                                 5 6))))
  ;; The same identity *is* registered at arity 2, so this fails only
  ;; because the lookup uses the arity the closure records. Dropping that
  ;; check would resolve it to the binary procedure and answer 11.
  (test-equal "the arity the closure records selects the procedure"
              11
              (%apply-closure (closure-session)
                              (funref-closure prelude-double 2)
                              5 6))
  (test-equal "lifted lambda dispatches with its captures"
              15
              (%apply-closure (closure-session)
                              (make-term '__closure (vector 'm__lambda_0 'src 10))
                              5))
  ;; The generated dispatchers read the header fields through `deref`
  ;; (their `equal?/chr` comparisons did), so a bound header field
  ;; still dispatches.
  (let* ((s (closure-session))
         (ident (make-var s))
         (arity (make-var s)))
    (%unify s ident prelude-double)
    (%unify s arity 1)
    (test-equal "a bound header field still dispatches"
                10
                (%apply-closure s (make-term '/ (vector ident arity)) 5)))
  (test-equal "unknown identity is a general failure"
              'general
              (failure-kind
               (lambda ()
                 (%apply-closure (closure-session)
                                 (funref-closure prelude-nope 1)
                                 5))))
  (test-equal "unbound closure is an instantiation failure"
              'inst
              (failure-kind
               (lambda () (%apply-closure (closure-session) (fresh-var) 5))))
  (test-equal "a non-closure is a general failure"
              'general
              (failure-kind (lambda () (%apply-closure (closure-session) 5 1))))
  (test-equal "a data term with a closure-looking field is not a closure"
              'general
              (failure-kind
               (lambda ()
                 (%apply-closure (closure-session)
                                 (make-term 'pair (vector prelude-double 1))
                                 5)))))

(test-end "runtime")
