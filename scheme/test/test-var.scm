(import (rnrs)
        (srfi :64)
        (ychr session)
        (ychr optable)
        (ychr var))

;; Helper: create a fresh session (var counter starts at 0)
;; Mirrors %make-session's empty dispatch tables, empty store index and
;; empty constraint-type-name table so this low-level test doesn't depend
;; on the runtime entry point. The operator table is the built-in one, the
;; default a hand-built session gets.
(define (fresh)
  (make-session (make-counters 0 0)
                (vector)
                (vector)
                (vector)
                (vector)
                #f
                '()
                '()
                (make-hashtable equal-hash equal?)
                (make-hashtable equal-hash equal?)
                (make-hashtable equal-hash equal?)
                builtin-op-table
                ;; Origin-less tell tier, then the three search tables.
                ;; The tier is empty: this session tells nothing.
                (make-hashtable equal-hash equal?)
                (make-hashtable equal-hash equal?)
                (make-hashtable equal-hash equal?)
                (make-hashtable equal-hash equal?)
                (vector)
                #f
                (vector)))

(test-begin "var")

;;; --------------------------------------------------------------------------
;;; Variable creation
;;; --------------------------------------------------------------------------

(test-group "make-var"
  (let* ((s (fresh))
         (x (make-var s))
         (y (make-var s)))
    (test-assert "returns a var" (var? x))
    (test-assert "distinct vars" (not (eq? x y)))
    (test-eqv "sequential ids" 0 (var-id x))
    (test-eqv "sequential ids" 1 (var-id y))))

;;; --------------------------------------------------------------------------
;;; Deref
;;; --------------------------------------------------------------------------

(test-group "deref"
  (test-group "unbound var derefs to itself"
    (let* ((s (fresh)) (x (make-var s)))
      (test-eq "identity" x (deref x))))

  (test-group "ground values deref to themselves"
    (test-eqv "integer" 42 (deref 42))
    (test-eq "symbol" 'foo (deref 'foo))
    (test-eq "boolean" #t (deref #t)))

  (test-group "follows binding chain"
    (let* ((s (fresh)) (x (make-var s)) (y (make-var s)))
      (unify x y)
      (unify y 42)
      (test-eqv "deref through chain" 42 (deref x))))

  (test-group "path compression"
    (let* ((s (fresh)) (x (make-var s)) (y (make-var s)) (z (make-var s)))
      (unify x y)
      (unify y z)
      (unify z 99)
      (test-eqv "deref reaches end" 99 (deref x))
      (test-eqv "compressed" 99 (deref x)))))

;;; --------------------------------------------------------------------------
;;; Unify — ground values
;;; --------------------------------------------------------------------------

(test-group "unify-ground"
  (test-group "integers"
    (let-values (((ok obs) (unify 1 1)))
      (test-assert "same int succeeds" ok)
      (test-assert "no observers" (null? obs)))
    (let-values (((ok obs) (unify 1 2)))
      (test-assert "different int fails" (not ok))))

  (test-group "symbols"
    (let-values (((ok obs) (unify 'a 'a)))
      (test-assert "same symbol succeeds" ok))
    (let-values (((ok obs) (unify 'a 'b)))
      (test-assert "different symbol fails" (not ok))))

  (test-group "booleans"
    (let-values (((ok obs) (unify #t #t)))
      (test-assert "same bool succeeds" ok))
    (let-values (((ok obs) (unify #t #f)))
      (test-assert "different bool fails" (not ok))))

  (test-group "strings"
    (let-values (((ok obs) (unify "hello" "hello")))
      (test-assert "same string succeeds" ok))
    (let-values (((ok obs) (unify "hello" "world")))
      (test-assert "different string fails" (not ok))))

  (test-group "type mismatches"
    (let-values (((ok obs) (unify 1 'a)))
      (test-assert "int vs symbol" (not ok)))
    (let-values (((ok obs) (unify #t 1)))
      (test-assert "bool vs int" (not ok)))
    (let-values (((ok obs) (unify "x" 'x)))
      (test-assert "string vs symbol" (not ok)))))

;;; --------------------------------------------------------------------------
;;; Unify — variables
;;; --------------------------------------------------------------------------

(test-group "unify-vars"
  (let ((s (fresh)))
    (test-group "var to ground"
      (let ((x (make-var s)))
        (let-values (((ok obs) (unify x 42)))
          (test-assert "succeeds" ok)
          (test-eqv "var bound" 42 (deref x)))))

    (test-group "ground to var"
      (let ((x (make-var s)))
        (let-values (((ok obs) (unify 42 x)))
          (test-assert "succeeds" ok)
          (test-eqv "var bound" 42 (deref x)))))

    (test-group "var to var"
      (let ((x (make-var s))
            (y (make-var s)))
        (let-values (((ok obs) (unify x y)))
          (test-assert "succeeds" ok))
        (unify y 7)
        (test-eqv "x follows through y" 7 (deref x))
        (test-eqv "y is bound" 7 (deref y))))

    (test-group "same var"
      (let ((x (make-var s)))
        (let-values (((ok obs) (unify x x)))
          (test-assert "succeeds" ok)
          (test-assert "still unbound" (var? (deref x))))))))

;;; --------------------------------------------------------------------------
;;; Unify — observer collection
;;; --------------------------------------------------------------------------

(test-group "unify-observers"
  (let ((s (fresh)))
    (test-group "binding emits observers"
      (let ((x (make-var s)))
        (add-observer! 10 x)
        (add-observer! 20 x)
        (let-values (((ok obs) (unify x 42)))
          (test-assert "succeeds" ok)
          (test-assert "observer 10 emitted" (memv 10 obs))
          (test-assert "observer 20 emitted" (memv 20 obs)))))

    (test-group "var-var merge emits first's observers"
      (let ((x (make-var s))
            (y (make-var s)))
        (add-observer! 1 x)
        (add-observer! 2 y)
        (let-values (((ok obs) (unify x y)))
          (test-assert "succeeds" ok)
          (test-assert "observer 1 emitted" (memv 1 obs)))))

    (test-group "no observers on ground unification"
      (let-values (((ok obs) (unify 5 5)))
        (test-assert "succeeds" ok)
        (test-assert "empty observers" (null? obs))))))

;;; --------------------------------------------------------------------------
;;; Unify — terms
;;; --------------------------------------------------------------------------

(test-group "unify-terms"
  (let ((s (fresh)))
    (test-group "same functor and args"
      (let-values (((ok obs) (unify (make-term 'f (vector 1 2))
                                    (make-term 'f (vector 1 2)))))
        (test-assert "succeeds" ok)))

    (test-group "different functor"
      (let-values (((ok obs) (unify (make-term 'f (vector 1))
                                    (make-term 'g (vector 1)))))
        (test-assert "fails" (not ok))))

    (test-group "different arity"
      (let-values (((ok obs) (unify (make-term 'f (vector 1))
                                    (make-term 'f (vector 1 2)))))
        (test-assert "fails" (not ok))))

    (test-group "recursive unification with variables"
      (let ((x (make-var s))
            (y (make-var s)))
        (let-values (((ok obs) (unify (make-term 'f (vector x 2))
                                      (make-term 'f (vector 1 y)))))
          (test-assert "succeeds" ok)
          (test-eqv "x bound to 1" 1 (deref x))
          (test-eqv "y bound to 2" 2 (deref y)))))

    (test-group "nested terms"
      (let ((x (make-var s)))
        (let-values (((ok obs) (unify (make-term 'f (vector (make-term 'g (vector x))))
                                      (make-term 'f (vector (make-term 'g (vector 99)))))))
          (test-assert "succeeds" ok)
          (test-eqv "x bound deeply" 99 (deref x)))))

    (test-group "term vs non-term"
      (let-values (((ok obs) (unify (make-term 'f (vector 1)) 42)))
        (test-assert "fails" (not ok))))))

;;; --------------------------------------------------------------------------
;;; Equal (ask semantics)
;;; --------------------------------------------------------------------------

(test-group "equal-ground"
  (test-assert "same int" (equal?/chr 1 1))
  (test-assert "diff int" (not (equal?/chr 1 2)))
  (test-assert "same symbol" (equal?/chr 'a 'a))
  (test-assert "diff symbol" (not (equal?/chr 'a 'b)))
  (test-assert "same bool" (equal?/chr #t #t))
  (test-assert "diff bool" (not (equal?/chr #t #f)))
  (test-assert "same string" (equal?/chr "hi" "hi"))
  (test-assert "diff string" (not (equal?/chr "hi" "ho")))
  (test-assert "type mismatch" (not (equal?/chr 1 'a))))

(test-group "equal-vars"
  (let ((s (fresh)))
    (test-group "same unbound var is equal to itself"
      (let ((x (make-var s)))
        (test-assert (equal?/chr x x))))

    (test-group "distinct unbound vars are NOT equal"
      (let ((x (make-var s))
            (y (make-var s)))
        (test-assert (not (equal?/chr x y)))))

    (test-group "bound var follows deref"
      (let ((x (make-var s)))
        (unify x 42)
        (test-assert "equal to its value" (equal?/chr x 42))
        (test-assert "not equal to other" (not (equal?/chr x 99)))))

    (test-group "two vars bound to same value"
      (let ((x (make-var s))
            (y (make-var s)))
        (unify x 10)
        (unify y 10)
        (test-assert (equal?/chr x y))))

    (test-group "unbound var not equal to ground"
      (let ((x (make-var s)))
        (test-assert (not (equal?/chr x 42)))))))

(test-group "equal-terms"
  (let ((s (fresh)))
    (test-assert "same term"
      (equal?/chr (make-term 'f (vector 1 2))
                  (make-term 'f (vector 1 2))))
    (test-assert "different functor"
      (not (equal?/chr (make-term 'f (vector 1))
                       (make-term 'g (vector 1)))))
    (test-assert "different arity"
      (not (equal?/chr (make-term 'f (vector 1))
                       (make-term 'f (vector 1 2)))))
    (test-assert "different args"
      (not (equal?/chr (make-term 'f (vector 1))
                       (make-term 'f (vector 2)))))
    (test-group "nested terms with bound vars"
      (let ((x (make-var s)))
        (unify x 'a)
        (test-assert
          (equal?/chr (make-term 'f (vector x))
                      (make-term 'f (vector 'a))))))))

;;; --------------------------------------------------------------------------
;;; match-term and get-arg
;;; --------------------------------------------------------------------------

(test-group "match-term"
  (let ((s (fresh)))
    (let ((t (make-term 'f (vector 1 2 3))))
      (test-assert "correct functor and arity" (match-term t 'f 3))
      (test-assert "wrong functor" (not (match-term t 'g 3)))
      (test-assert "wrong arity" (not (match-term t 'f 2)))
      (test-assert "non-term" (not (match-term 42 'f 1))))

    (test-group "through deref"
      (let ((x (make-var s))
            (t (make-term 'g (vector 'a))))
        (unify x t)
        (test-assert (match-term x 'g 1))))))

(test-group "get-arg"
  (let ((s (fresh)))
    (let ((t (make-term 'f (vector 10 20 30))))
      (test-eqv "arg 0" 10 (get-arg t 0))
      (test-eqv "arg 1" 20 (get-arg t 1))
      (test-eqv "arg 2" 30 (get-arg t 2)))

    (test-group "through deref"
      (let ((x (make-var s))
            (t (make-term 'h (vector 'ok))))
        (unify x t)
        (test-eq "arg through var" 'ok (get-arg x 0))))))

;;; --------------------------------------------------------------------------
;;; add-observer!
;;; --------------------------------------------------------------------------

(test-group "add-observer"
  (let ((s (fresh)))
    (test-group "adds to unbound var"
      (let ((x (make-var s)))
        (add-observer! 5 x)
        (add-observer! 6 x)
        (let-values (((ok obs) (unify x 1)))
          (test-assert "observer 5" (memv 5 obs))
          (test-assert "observer 6" (memv 6 obs)))))

    (test-group "no-op on bound var"
      (let ((x (make-var s)))
        (unify x 42)
        (add-observer! 7 x)
        (test-assert "bound var" #t)))

    (test-group "no-op on non-var"
      (add-observer! 8 42)
      (test-assert "non-var" #t))))

;;; --------------------------------------------------------------------------
;;; get-var-id
;;; --------------------------------------------------------------------------

(test-group "get-var-id"
  (let* ((s (fresh))
         (x (make-var s))
         (y (make-var s)))
    (test-eqv "unbound var id" 0 (get-var-id x))
    (test-eqv "unbound var id" 1 (get-var-id y))
    (unify x 42)
    (test-eq "bound var returns #f" #f (get-var-id x))
    (test-eq "non-var returns #f" #f (get-var-id 99))))

;;; --------------------------------------------------------------------------
;;; unifiable?
;;; --------------------------------------------------------------------------

(test-group "unifiable?"
  (test-group "ground vs ground"
    (test-eq "same int"      #t (unifiable? 1 1))
    (test-eq "distinct ints" #f (unifiable? 1 2))
    (test-eq "same atom"     #t (unifiable? 'a 'a))
    (test-eq "distinct atom" #f (unifiable? 'a 'b))
    (test-eq "type mismatch" #f (unifiable? 1 'a)))

  (test-group "unbound var vs ground leaves var unbound"
    (let* ((s (fresh)) (x (make-var s)))
      (test-eq "returns true" #t (unifiable? x 42))
      (test-eq "var still unbound" x (deref x))
      (test-eqv "var id preserved" 0 (get-var-id x))))

  (test-group "ground vs unbound var leaves var unbound"
    (let* ((s (fresh)) (x (make-var s)))
      (test-eq "returns true" #t (unifiable? 42 x))
      (test-eq "var still unbound" x (deref x))))

  (test-group "two distinct unbound vars"
    (let* ((s (fresh)) (x (make-var s)) (y (make-var s)))
      (test-eq "returns true" #t (unifiable? x y))
      (test-eq "x still unbound" x (deref x))
      (test-eq "y still unbound" y (deref y))))

  (test-group "same unbound var with itself"
    (let* ((s (fresh)) (x (make-var s)))
      (test-eq "returns true" #t (unifiable? x x))
      (test-eq "still unbound" x (deref x))))

  (test-group "compound: matching args"
    (let* ((s (fresh)) (x (make-var s)))
      (let ((t1 (make-term 'f (vector x 1)))
            (t2 (make-term 'f (vector 2 1))))
        (test-eq "returns true" #t (unifiable? t1 t2))
        (test-eq "x still unbound" x (deref x)))))

  (test-group "compound: mismatched functor"
    (test-eq #f (unifiable? (make-term 'f (vector 1))
                            (make-term 'g (vector 1)))))

  (test-group "compound: mismatched arity"
    (test-eq #f (unifiable? (make-term 'f (vector 1))
                            (make-term 'f (vector 1 2)))))

  (test-group "compound: nested failure rolls back"
    ;; f(X, 1) vs f(2, 3) — walk binds X to 2, then fails on 1 vs 3.
    ;; X must still be unbound after the call.
    (let* ((s (fresh)) (x (make-var s)))
      (let ((t1 (make-term 'f (vector x 1)))
            (t2 (make-term 'f (vector 2 3))))
        (test-eq "returns false" #f (unifiable? t1 t2))
        (test-eq "x still unbound" x (deref x))
        (test-eqv "var id preserved" 0 (get-var-id x)))))

  (test-group "compound: double-bind failure rolls back"
    ;; f(X, X) vs f(1, 2) — X bound to 1, then fails on X=2.
    (let* ((s (fresh)) (x (make-var s)))
      (let ((t1 (make-term 'f (vector x x)))
            (t2 (make-term 'f (vector 1 2))))
        (test-eq "returns false" #f (unifiable? t1 t2))
        (test-eq "x still unbound" x (deref x)))))

  (test-group "transitively unifiable: f(X, X) vs f(1, 1)"
    (let* ((s (fresh)) (x (make-var s)))
      (let ((t1 (make-term 'f (vector x x)))
            (t2 (make-term 'f (vector 1 1))))
        (test-eq "returns true" #t (unifiable? t1 t2))
        (test-eq "x still unbound" x (deref x)))))

  (test-group "pre-bound var stays bound"
    ;; Bind X to 7, then check that a failing unifiable? does not
    ;; disturb the existing binding.
    (let* ((s (fresh)) (x (make-var s)))
      (unify x 7)
      (test-eq "returns false" #f (unifiable? x 8))
      (test-eqv "still bound to 7" 7 (deref x)))))

;;; --------------------------------------------------------------------------
;;; Native lists: a `prelude__.` cell is a pair and nil is '()
;;; --------------------------------------------------------------------------

(test-group "native-lists"
  (define cons-f (string->symbol "prelude__."))
  (define nil-s (string->symbol "prelude__[]"))

  (test-group "make-term builds a pair for a cons cell"
    (let ((l (make-term cons-f (vector 1 '()))))
      (test-assert "is a pair" (pair? l))
      (test-equal "is (1)" '(1) l)
      (test-assert "is a term" (term? l))
      (test-eq "functor" cons-f (term-functor l))
      (test-equal "args" (vector 1 '()) (term-args l))))

  (test-group "the bare . functor stays a record"
    (let ((l (make-term '|.| (vector 1 '()))))
      (test-assert "not a pair" (not (pair? l)))
      (test-assert "not equal to the native cell"
                   (not (equal?/chr l (list 1))))))

  (test-group "match-term and get-arg"
    (let ((l (list 1 2)))
      (test-assert "cons/2" (match-term l cons-f 2))
      (test-assert "not cons/1" (not (match-term l cons-f 1)))
      (test-assert "nil/0" (match-term '() nil-s 0))
      (test-assert "nil is not the bare []"
                   (not (match-term '() (string->symbol "[]") 0)))
      (test-eqv "head" 1 (get-arg l 0))
      (test-equal "tail" '(2) (get-arg l 1))))

  (test-group "unify binds through pairs"
    (let* ((s (fresh)) (x (make-var s)) (t (make-var s)))
      (let-values (((ok obs) (unify (cons x t) (list 1 2 3))))
        (test-assert "succeeds" ok)
        (test-eqv "head" 1 (deref x))
        (test-equal "tail" '(2 3) (deref t)))))

  (test-group "unify fails on length mismatch"
    (let-values (((ok obs) (unify (list 1 2) (list 1))))
      (test-assert "fails" (not ok))))

  (test-group "nil unifies only with nil"
    (let-values (((ok obs) (unify '() '())))
      (test-assert "nil = nil" ok))
    (let-values (((ok obs) (unify '() nil-s)))
      (test-assert "nil is not the symbol" (not ok))))

  (test-group "unifiable? on pairs leaves no binding"
    (let* ((s (fresh)) (x (make-var s)))
      (test-assert "unifiable" (unifiable? (list x 2) (list 1 2)))
      (test-eq "x still unbound" x (deref x))))

  (test-group "equal?/chr on pairs"
    (test-assert "equal" (equal?/chr (list 1 'a) (list 1 'a)))
    (test-assert "different" (not (equal?/chr (list 1 'a) (list 1 'b))))
    (test-assert "nil" (equal?/chr '() '())))

  (test-group "a pair and its record spelling have the same key"
    (test-equal "ground keys agree"
                (ground-key (list 1 2))
                (list 'term cons-f '(num . 1)
                      (list 'term cons-f '(num . 2) (cons 'atom nil-s))))
    (test-equal "nil keys as the nil atom" (cons 'atom nil-s) (ground-key '()))
    (let* ((s (fresh)) (x (make-var s)))
      (test-assert "partial list is not ground" (not (ground-key (cons 1 x))))))

  (test-group "atoms"
    (test-assert "nil is an atom" (chr-atom? '()))
    (test-eq "nil's name" nil-s (atom->symbol '()))
    (test-eq "back to nil" '() (symbol->atom nil-s))
    (test-eq "other symbols unchanged" 'a (symbol->atom 'a))))

;;; --------------------------------------------------------------------------
;;; Flat compounds: one record type per arity up to K, a vector above
;;; --------------------------------------------------------------------------

(test-group "flat-compounds"
  (define (args-up-to n)
    (let ((v (make-vector n)))
      (do ((i 0 (+ i 1))) ((= i n) v) (vector-set! v i (* 10 (+ i 1))))))

  (test-eqv "K is 8" 8 compound-max-flat-arity)

  (test-group "round trip at every arity"
    (do ((n 1 (+ n 1))) ((> n 12))
      (let* ((args (args-up-to n)) (t (make-term 'f args)))
        (test-assert "term?" (term? t))
        (test-assert "compound?" (compound? t))
        (test-eq "functor" 'f (term-functor t))
        (test-eqv "arity" n (term-arity t))
        (test-equal "args" args (term-args t))
        (do ((i 0 (+ i 1))) ((= i n))
          (test-eqv "arg" (vector-ref args i) (term-arg t i)))
        (test-assert "match-term" (match-term t 'f n))
        (test-assert "match-term other arity"
                     (not (match-term t 'f (+ n 1)))))))

  (test-group "boundary K and K + 1"
    (let ((k (make-term 'f (args-up-to 8)))
          (k1 (make-term 'f (args-up-to 9))))
      (test-assert "K is flat" (compound8? k))
      (test-assert "K is not compound*" (not (compound*? k)))
      (test-assert "K + 1 is compound*" (compound*? k1))
      (test-eqv "K + 1 vector" 9 (vector-length (compound*-args k1)))))

  (test-group "one representation per arity"
    (test-assert "arity 2" (compound2? (make-term 'f (vector 1 2))))
    (test-assert "arity 3" (compound3? (make-term 'f (vector 1 2 3))))
    (test-assert "make-compound2 equals make-term"
                 (equal?/chr (make-compound2 'f 1 2)
                             (make-term 'f (vector 1 2)))))

  (test-group "nullary make-term is an empty compound*"
    ;; As the reference's `VTerm t []` for a nullary constraint.
    (let ((t (make-term 'f (vector))))
      (test-assert "compound*" (compound*? t))
      (test-eqv "arity" 0 (term-arity t))
      (test-assert "not the atom" (not (equal?/chr t 'f)))))

  (test-group "unify across shapes"
    (let* ((s (fresh)) (x (make-var s)))
      (test-assert "compound3 vs compound3, other functor"
                   (not (let-values (((ok obs)
                                      (unify (make-term 'f (vector 1 2 3))
                                             (make-term 'g (vector 1 2 3)))))
                          ok)))
      (test-assert "compound3 vs compound2"
                   (not (let-values (((ok obs)
                                      (unify (make-term 'f (vector 1 2 3))
                                             (make-term 'f (vector 1 2)))))
                          ok)))
      (test-assert "K + 1 binds"
                   (let-values (((ok obs)
                                 (unify (make-term 'f (args-up-to 9))
                                        (make-term 'f (vector 10 20 30 40 50 60
                                                              70 80 x)))))
                     ok))
      (test-eqv "x bound" 90 (deref x))
      (test-assert "equal?/chr K + 1"
                   (equal?/chr (make-term 'f (args-up-to 9))
                               (make-term 'f (args-up-to 9))))
      (test-assert "unifiable? compound3 vs compound2"
                   (not (unifiable? (make-term 'f (vector 1 2 3))
                                    (make-term 'f (vector 1 2)))))))

  (test-group "term-map"
    (do ((n 1 (+ n 1))) ((> n 10))
      (let ((t (term-map (lambda (a) (+ a 1)) (make-term 'f (args-up-to n)))))
        (test-eqv "arity" n (term-arity t))
        (test-eqv "first arg" 11 (term-arg t 0)))))

  (test-group "get-arg on a bound variable"
    (let* ((s (fresh)) (x (make-var s)))
      (unify x (make-term 'f (vector 1 2 3 4)))
      (test-eqv "arg 3" 4 (get-arg x 3)))))

;; A typed functor (its name holds `__`) has one record type per arity,
;; whoever builds the term.
(test-group "typed functor types"
  (let ((rtd (lambda (t) (record-rtd t))))
    (test-assert "make-term and the constructor share a type"
      (eq? (rtd (make-term 'm__f (vector 1 2)))
           (rtd ((compound-constructor 'm__f 2) 3 4))))
    (test-assert "make-compound2 too"
      (eq? (rtd (make-compound2 'm__f 1 2)) (rtd (make-term 'm__f (vector 5 6)))))
    (test-assert "term-map keeps the type"
      (let ((t (make-term 'm__g (vector 1 2 3))))
        (eq? (rtd t) (rtd (term-map (lambda (x) x) t)))))
    (test-assert "another arity is another type"
      (not (eq? (rtd (make-term 'm__f (vector 1)))
                (rtd (make-term 'm__f (vector 1 2))))))
    (test-assert "another functor is another type"
      (not (eq? (rtd (make-term 'm__f (vector 1 2)))
                (rtd (make-term 'm__g (vector 1 2))))))
    (test-eq "the functor is the type's name" 'm__h
      (term-functor (make-term 'm__h (vector 1))))
    (test-eq "an odd functor name" (string->symbol "m__x y")
      (term-functor (make-term (string->symbol "m__x y") (vector 1 2 3))))
    (test-eq "arity above K" 'm__big
      (term-functor (make-term 'm__big (vector 1 2 3 4 5 6 7 8 9))))
    (test-assert "predicate"
      (and ((compound-predicate 'm__f 2) (make-term 'm__f (vector 1 2)))
           (not ((compound-predicate 'm__f 2) (make-term 'm__g (vector 1 2))))
           (not ((compound-predicate 'm__f 2) (make-term 'm__f (vector 1))))))
    (test-assert "compound* of two arities: not the same shape"
      (let-values (((ok obs) (unify (make-term 'm__f (vector 1 2 3 4 5 6 7 8 9))
                                    (make-term 'm__f (vector 1 2 3 4 5 6 7 8 9 10)))))
        (not ok)))
    (test-assert "match-compound*"
      (and (match-compound* (make-term 'm__f (vector 1 2 3 4 5 6 7 8 9))
                            (compound-predicate 'm__f 9) 9)
           (not (match-compound* (make-term 'm__f (vector 1 2 3 4 5 6 7 8 9 10))
                                 (compound-predicate 'm__f 9) 9))))
    (test-assert "match-term2 by functor"
      (and (match-term2 (make-term 'm__f (vector 1 2)) 'm__f)
           (not (match-term2 (make-term 'm__f (vector 1 2)) 'm__g))))))

;; Bare functors (no `__`) share one record type per arity; the functor
;; is a field. So a new functor name costs no new type.
(test-group "bare functor types"
  (let ((rtd (lambda (t) (record-rtd t)))
        (args (lambda (n)
                (let ((v (make-vector n)))
                  (do ((i 0 (+ i 1))) ((= i n) v) (vector-set! v i (+ i 1)))))))
    (do ((n 1 (+ n 1))) ((> n 10))
      (let ((f (make-term 'f (args n))) (g (make-term 'g (args n))))
        (test-assert "two functors, one type" (eq? (rtd f) (rtd g)))
        (test-eq "functor" 'f (term-functor f))
        (test-eqv "arity" n (term-arity f))
        (test-eqv "last arg" n (term-arg f (- n 1)))
        (test-assert "match-term"
          (and (match-term f 'f n) (not (match-term f 'g n))
               (not (match-term f 'f (+ n 1)))))
        (test-assert "equal to itself rebuilt"
          (equal?/chr f (make-term 'f (args n))))
        (test-assert "not equal to another functor" (not (equal?/chr f g)))
        (test-assert "does not unify with another functor"
          (let-values (((ok obs) (unify f g))) (not ok)))
        (test-assert "not unifiable with another functor"
          (not (unifiable? f g)))
        (test-assert "not equal to a typed functor"
          (not (equal?/chr f (make-term 'm__f (args n)))))
        (test-assert "predicate"
          (and ((compound-predicate 'f n) f)
               (not ((compound-predicate 'f n) g))
               (not ((compound-predicate 'f n) (make-term 'm__f (args n))))))
        (test-assert "constructor"
          (equal?/chr f (if (> n 8)
                            ((compound-constructor 'f n) (args n))
                            (apply (compound-constructor 'f n)
                                   (vector->list (args n))))))
        (test-assert "term-map keeps the functor"
          (equal?/chr f (term-map (lambda (x) x) f)))
        (test-assert "ground key"
          (and (equal? (ground-key f) (ground-key (make-term 'f (args n))))
               (not (equal? (ground-key f) (ground-key g)))))))
    (test-assert "another arity is another type"
      (not (eq? (rtd (make-term 'f (vector 1))) (rtd (make-term 'f (vector 1 2))))))
    (test-assert "typed and bare differ"
      (not (eq? (rtd (make-term 'f (vector 1 2)))
                (rtd (make-term 'm__f (vector 1 2))))))
    (test-assert "make-compound2"
      (equal?/chr (make-compound2 'f 1 2) (make-term 'f (vector 1 2))))
    (test-assert "match-term2 by functor"
      (and (match-term2 (make-term 'f (vector 1 2)) 'f)
           (not (match-term2 (make-term 'f (vector 1 2)) 'g))))
    (test-assert "match-compound*"
      (and (match-compound* (make-term 'f (args 9)) (compound-predicate 'f 9) 9)
           (not (match-compound* (make-term 'f (args 10))
                                 (compound-predicate 'f 9) 9))
           (not (match-compound* (make-term 'g (args 9))
                                 (compound-predicate 'f 9) 9))))
    (test-assert "compound* of two arities: not the same shape"
      (let-values (((ok obs) (unify (make-term 'f (args 9))
                                    (make-term 'f (args 10)))))
        (not ok)))
    (test-eq "an odd functor name" (string->symbol "x y")
      (term-functor (make-term (string->symbol "x y") (vector 1 2 3))))
    (test-eq "a single underscore is bare" 'a_b
      (term-functor (make-term 'a_b (vector 1))))
    (test-assert "a single underscore shares the bare type"
      (eq? (rtd (make-term 'a_b (vector 1))) (rtd (make-term 'f (vector 1)))))
    (test-eqv "nullary compound*" 0 (term-arity (make-term 'f (vector))))
    (test-eq "nullary compound* functor" 'f (term-functor (make-term 'f (vector))))))

;;; --------------------------------------------------------------------------
;;; unifiable-oc?: unifiable? plus an occurs check
;;; --------------------------------------------------------------------------

;; Is `v` still unbound after the check?
(define (unbound? v) (var? (deref v)))

;; A term of arity n with `x` nested one level down in its last slot.
(define (deep-in f n x)
  (let ((v (make-vector n 0)))
    (vector-set! v (- n 1) (make-term f (vector x)))
    (make-term f v)))

(test-group "unifiable-oc?"
  (let ((s (fresh)))
    (let ((x (make-var s)) (y (make-var s)))
      (test-eq "X vs f(X)" #f (unifiable-oc? x (make-term 'f (vector x))))
      (test-eq "f(X) vs X" #f (unifiable-oc? (make-term 'f (vector x)) x))
      (test-eq "X vs [a | X]" #f (unifiable-oc? x (cons 'a x)))
      (test-eq "f(X, Y) vs f(Y, g(X))" #f
        (unifiable-oc? (make-term 'f (vector x y))
                       (make-term 'f (vector y (make-term 'g (vector x))))))
      (test-eq "X vs Y" #t (unifiable-oc? x y))
      (test-eq "X vs X" #t (unifiable-oc? x x))
      (test-eq "f(X) vs f(g(Y))" #t
        (unifiable-oc? (make-term 'f (vector x))
                       (make-term 'f (vector (make-term 'g (vector y))))))
      (test-eq "f(a) vs f(b)" #f
        (unifiable-oc? (make-term 'f (vector 'a)) (make-term 'f (vector 'b))))
      (test-eq "functor mismatch" #f
        (unifiable-oc? (make-term 'f (vector 1)) (make-term 'g (vector 1))))
      (test-eq "arity mismatch" #f
        (unifiable-oc? (make-term 'f (vector 1)) (make-term 'f (vector 1 2))))
      (test-assert "X still unbound" (unbound? x))
      (test-assert "Y still unbound" (unbound? y)))

    (test-group "deep occurrences, bare and typed, arity 1, 8, 9"
      (let ((x (make-var s)))
        (for-each
          (lambda (f)
            (for-each
              (lambda (n)
                (test-eq "occurs" #f (unifiable-oc? x (deep-in f n x)))
                (test-eq "does not occur" #t
                  (unifiable-oc? x (deep-in f n 1))))
              '(1 8 9)))
          '(f m__t))
        (test-eq "list tail" #f (unifiable-oc? x (cons* 1 2 x)))
        (test-assert "X still unbound" (unbound? x))))

    (test-group "alias chain made before the call"
      (let ((v (make-var s)) (w (make-var s)))
        (unify w v)
        (test-eq "W vs f(V)" #f (unifiable-oc? w (make-term 'f (vector v))))
        (test-assert "V still unbound" (unbound? v))
        (unify v 9)
        (test-eqv "alias kept" 9 (deref w))))

    (test-group "observers are not touched"
      (let ((x (make-var s)))
        (add-observer! 1 x)
        (add-observer! 2 x)
        (unifiable-oc? x 1)
        (unifiable-oc? x (make-term 'f (vector x)))
        (let-values (((ok obs) (unify x 1)))
          (test-assert "succeeds" ok)
          (test-equal "same observers" '(1 2) (list-sort < obs)))))))

;;; --------------------------------------------------------------------------
;;; Floats: equal flonums unify
;;; --------------------------------------------------------------------------

(test-group "floats"
  (test-eq "unifiable? 1.5 1.5" #t (unifiable? 1.5 1.5))
  (test-eq "unifiable-oc? 1.5 1.5" #t (unifiable-oc? 1.5 1.5))
  (test-eq "unifiable? 1 1.0" #f (unifiable? 1 1.0))
  (test-eq "unifiable? \"a\" a" #f (unifiable? "a" 'a))
  (let-values (((ok obs) (unify 1.5 1.5)))
    (test-assert "unify 1.5 1.5" ok))
  (let-values (((ok obs) (unify 2.0 2.0)))
    (test-assert "unify 2.0 2.0" ok))
  (let-values (((ok obs) (unify 1 1.0)))
    (test-assert "unify 1 1.0 fails" (not ok))))

(test-end "var")
