;;;; Logical variables, compound terms, unification, and equality.
(library (ychr var)
  (export make-var
          var?
          var-id
          deref
          unify
          unifiable?
          equal?/chr
          make-term
          term?
          term-functor
          term-args
          term-arity
          term-arg
          term-map
          ground?
          compound?
          compound-functor
          compound-max-flat-arity
          compound-constructor compound-predicate
          match-compound*
          ;; The parent record types, for `define-record-type` in a
          ;; `scheme-types` records library.
          compound1 compound2 compound3 compound4
          compound5 compound6 compound7 compound8
          make-compound1 compound1? compound1-a1
          make-compound2 compound2? compound2-a1 compound2-a2
          make-compound3 compound3? compound3-a1 compound3-a2 compound3-a3
          make-compound4 compound4? compound4-a1 compound4-a2 compound4-a3
          compound4-a4
          make-compound5 compound5? compound5-a1 compound5-a2 compound5-a3
          compound5-a4 compound5-a5
          make-compound6 compound6? compound6-a1 compound6-a2 compound6-a3
          compound6-a4 compound6-a5 compound6-a6
          make-compound7 compound7? compound7-a1 compound7-a2 compound7-a3
          compound7-a4 compound7-a5 compound7-a6 compound7-a7
          make-compound8 compound8? compound8-a1 compound8-a2 compound8-a3
          compound8-a4 compound8-a5 compound8-a6 compound8-a7 compound8-a8
          make-compound* compound*? compound*-args
          match-term1 match-term2 match-term3 match-term4
          match-term5 match-term6 match-term7 match-term8
          cons-functor
          nil-symbol
          chr-atom?
          atom->symbol
          symbol->atom
          match-term
          get-arg
          add-observer!
          var-observers
          var-value
          add-observer-and-key
          ground-key
          get-var-id)
  (import (rnrs)
          (ychr session)
          (ychr trail))

  ;;; Logical variables
  (define *unbound* (list 'unbound))

  (define-record-type (var %make-var var?)
    (nongenerative ychr:var:1)
    (fields (immutable id var-id)
            (mutable value var-value var-value-set!)
            (mutable observers var-observers var-observers-set!)))

  (define (make-var s)
    (let ((id (session-var-id s)))
      (session-var-id-set! s (+ id 1))
      (%make-var id *unbound* '())))

  ;;; Trail one variable cell, immediately before it is overwritten.
  ;;; Two helpers rather than one because a write changes only one of the
  ;;; two cells, and trailing the other would restore a value it still
  ;;; holds. Each reads the old value only when a search is active.
  (define (trail-value! v)
    (when (trail-active?)
      (let ((old (var-value v)))
        (trail-push! (lambda () (var-value-set! v old))))))
  (define (trail-observers! v)
    (when (trail-active?)
      (let ((old (var-observers v)))
        (trail-push! (lambda () (var-observers-set! v old))))))

  ;;; Compound terms
  ;;;
  ;;; A CHR list is a native Scheme list: the cons cell
  ;;; `prelude__.`(H, T) is a pair and the nil atom `prelude__[]` is
  ;;; `'()`. Every other compound is a `compound` record.
  ;;;
  ;;; Every other compound is flat: its record type is a child of
  ;;; `compoundn` (the arguments as fields) for arity n <= K, or of
  ;;; `compound*` (a vector) above K. Which child depends on the
  ;;; functor's name only (see "Functor types"): a name that holds `__`
  ;;; has its own type, any other name shares one type per arity and
  ;;; keeps the functor in a field. A term has one representation only,
  ;;; so two terms of the same functor and arity always have the same
  ;;; record type. A nullary term is an atom; the
  ;;; one exception is the empty `compound*` `make-term` builds for a
  ;;; nullary constraint in `write_store_to_list`.
  ;;;
  ;;; `term?`, `term-functor`, `term-arity`, `term-arg` and `make-term`
  ;;; hide the split, so generic code sees a pair as a 2-ary
  ;;; `prelude__.` term. All of them take a dereferenced term.
  ;;; `term-args` builds a fresh vector every time: cold paths only.
  ;;;
  ;;; Only the canonical spellings map to pairs. The bare `.`/2 and `[]`
  ;;; that the reader builds stay a record and a symbol, as they are
  ;;; distinct values on the Haskell side too.
  ;;;
  ;;; The record types are nongenerative, with a versioned uid: a
  ;;; ground term written with Chez's `fasl-write` reads back in another
  ;;; process. Bump the suffix when a layout changes.
  (define cons-functor (string->symbol "prelude__."))
  (define nil-symbol (string->symbol "prelude__[]"))

  ;;; K, the largest arity with a flat record type. Keep in sync with
  ;;; `flatMaxArity` in src/YCHR/Internal/Backend/Scheme.hs.
  (define compound-max-flat-arity 8)

  (define-record-type (compound1 %make-compound1 compound1?)
    (nongenerative ychr:compound1:3)
    (fields (immutable a1 compound1-a1)))

  (define-record-type (compound2 %make-compound2 compound2?)
    (nongenerative ychr:compound2:3)
    (fields (immutable a1 compound2-a1) (immutable a2 compound2-a2)))

  (define-record-type (compound3 %make-compound3 compound3?)
    (nongenerative ychr:compound3:3)
    (fields (immutable a1 compound3-a1) (immutable a2 compound3-a2) (immutable a3 compound3-a3)))

  (define-record-type (compound4 %make-compound4 compound4?)
    (nongenerative ychr:compound4:3)
    (fields (immutable a1 compound4-a1) (immutable a2 compound4-a2) (immutable a3 compound4-a3) (immutable a4 compound4-a4)))

  (define-record-type (compound5 %make-compound5 compound5?)
    (nongenerative ychr:compound5:3)
    (fields (immutable a1 compound5-a1) (immutable a2 compound5-a2) (immutable a3 compound5-a3) (immutable a4 compound5-a4) (immutable a5 compound5-a5)))

  (define-record-type (compound6 %make-compound6 compound6?)
    (nongenerative ychr:compound6:3)
    (fields (immutable a1 compound6-a1) (immutable a2 compound6-a2) (immutable a3 compound6-a3) (immutable a4 compound6-a4) (immutable a5 compound6-a5) (immutable a6 compound6-a6)))

  (define-record-type (compound7 %make-compound7 compound7?)
    (nongenerative ychr:compound7:3)
    (fields (immutable a1 compound7-a1) (immutable a2 compound7-a2) (immutable a3 compound7-a3) (immutable a4 compound7-a4) (immutable a5 compound7-a5) (immutable a6 compound7-a6) (immutable a7 compound7-a7)))

  (define-record-type (compound8 %make-compound8 compound8?)
    (nongenerative ychr:compound8:3)
    (fields (immutable a1 compound8-a1) (immutable a2 compound8-a2) (immutable a3 compound8-a3) (immutable a4 compound8-a4) (immutable a5 compound8-a5) (immutable a6 compound8-a6) (immutable a7 compound8-a7) (immutable a8 compound8-a8)))

  (define-record-type (compound* %make-compound* compound*?)
    (nongenerative ychr:compound*:3)
    (fields (immutable args compound*-args)))

  ;;; Functor types
  ;;;
  ;;; The types above are parents. A term's own type is a sealed child,
  ;;; and the functor's name picks which:
  ;;;
  ;;; - Typed: the name holds `__` (`m__f`, `__closure`). The functor
  ;;;   gets its own child per arity, with no fields, named after it:
  ;;;   the functor is the type's name. Arities above K share one child
  ;;;   per functor under `compound*`. These are the names of declared
  ;;;   things, so a program has a fixed set of them, and a generated
  ;;;   library can define the type statically.
  ;;; - Bare: any other name (`foo`, `:`, what `list_to_compound` or the
  ;;;   reader make from data). All bare functors share one child per
  ;;;   arity, `dynN`, with the functor in one more field.
  ;;;
  ;;; Why two: a typed functor's type is never freed (its uid pins it),
  ;;; so a type per bare functor would grow with the data. The rule
  ;;; looks at the name only, so every library, process and fasl file
  ;;; picks the same representation.
  ;;;
  ;;; A typed child is made the first time it is asked for, and cached.
  ;;; Its uid is fixed by the functor and the arity, so every library
  ;;; and process gets the same type (fasl relies on it too). Always
  ;;; make one through `compound-type`: Chez keeps the name of the first
  ;;; type with a uid, so the name must be the functor every time.

  ;;; Whether `f` holds `__`.
  (define (name-typed? f)
    (let* ((s (symbol->string f)) (n (- (string-length s) 1)))
      (let loop ((i 0))
        (and (< i n)
             (or (and (char=? (string-ref s i) #\_)
                      (char=? (string-ref s (+ i 1)) #\_))
                 (loop (+ i 1)))))))

  ;;; `name-typed?`, behind a small direct-mapped cache. Fixed size, so
  ;;; it does not grow with the number of functors.
  (define functor-cache-mask 255)
  (define functor-cache-keys (make-vector (+ functor-cache-mask 1) #f))
  (define functor-cache-vals (make-vector (+ functor-cache-mask 1) #f))

  (define (typed-functor? f)
    (let ((h (bitwise-and (symbol-hash f) functor-cache-mask)))
      (if (eq? (vector-ref functor-cache-keys h) f)
          (vector-ref functor-cache-vals h)
          (let ((v (name-typed? f)))
            (vector-set! functor-cache-keys h f)
            (vector-set! functor-cache-vals h v)
            v))))

  ;;; The bare types. They all have the same name, `ychr:dyn`, which
  ;;; holds no `__` and so is no typed functor's name: one `eq?` on a
  ;;; type's name tells a bare term from a typed one. Each use of the
  ;;; macro binds its own `ychr:dyn`.
  (define-syntax define-dyn
    (syntax-rules ()
      ((_ p uid make pred functor-of)
       (define-record-type (ychr:dyn make pred)
         (parent p) (sealed #t) (nongenerative uid)
         (fields (immutable functor functor-of))))))

  (define dyn-name 'ychr:dyn)

  (define-dyn compound1 ychr:dyn1:1 %make-dyn1 dyn1? dyn1-functor)
  (define-dyn compound2 ychr:dyn2:1 %make-dyn2 dyn2? dyn2-functor)
  (define-dyn compound3 ychr:dyn3:1 %make-dyn3 dyn3? dyn3-functor)
  (define-dyn compound4 ychr:dyn4:1 %make-dyn4 dyn4? dyn4-functor)
  (define-dyn compound5 ychr:dyn5:1 %make-dyn5 dyn5? dyn5-functor)
  (define-dyn compound6 ychr:dyn6:1 %make-dyn6 dyn6? dyn6-functor)
  (define-dyn compound7 ychr:dyn7:1 %make-dyn7 dyn7? dyn7-functor)
  (define-dyn compound8 ychr:dyn8:1 %make-dyn8 dyn8? dyn8-functor)
  (define-dyn compound* ychr:dyn*:1 %make-dyn* dyn*? dyn*-functor)

  ;;; The functor of a bare term.
  (define (dyn-functor t)
    (cond ((dyn2? t) (dyn2-functor t)) ((dyn1? t) (dyn1-functor t))
          ((dyn3? t) (dyn3-functor t)) ((dyn4? t) (dyn4-functor t))
          ((dyn5? t) (dyn5-functor t)) ((dyn6? t) (dyn6-functor t))
          ((dyn7? t) (dyn7-functor t)) ((dyn8? t) (dyn8-functor t))
          (else (dyn*-functor t))))

  (define compound-parents
    (vector (record-type-descriptor compound*)
            (record-type-descriptor compound1) (record-type-descriptor compound2)
            (record-type-descriptor compound3) (record-type-descriptor compound4)
            (record-type-descriptor compound5) (record-type-descriptor compound6)
            (record-type-descriptor compound7) (record-type-descriptor compound8)))

  ;;; The typed functors' types. Slot 0 is `compound*`, slots 1..K the
  ;;; flat arities.
  (define compound-types
    (let ((v (make-vector (+ compound-max-flat-arity 1))))
      (do ((i 0 (+ i 1))) ((> i compound-max-flat-arity) v)
        (vector-set! v i (make-eq-hashtable)))))

  (define (type-slot n) (if (or (= n 0) (> n compound-max-flat-arity)) 0 n))

  ;;; The last functor asked for in each slot, and its entry: building
  ;;; many terms of one functor skips the table.
  (define last-functors (make-vector (+ compound-max-flat-arity 1) #f))
  (define last-entries (make-vector (+ compound-max-flat-arity 1) #f))

  ;;; The cached `#(rtd constructor predicate)` of the typed functor `f`
  ;;; at arity `n`. The constructor takes the arguments (a vector for
  ;;; `compound*`).
  (define (compound-type f n)
    (let ((k (type-slot n)))
      (if (eq? (vector-ref last-functors k) f)
          (vector-ref last-entries k)
          (let ((e (compound-type/table f k)))
            (vector-set! last-functors k f)
            (vector-set! last-entries k e)
            e))))

  (define (compound-type/table f k)
    (let ((tbl (vector-ref compound-types k)))
      (or (hashtable-ref tbl f #f)
          (let* ((uid (string->symbol
                       (string-append "ychr:c" (if (= k 0) "*" (number->string k))
                                      ":" (symbol->string f) ":1")))
                 (rtd (make-record-type-descriptor
                       f (vector-ref compound-parents k) uid #t #f '#()))
                 (e (vector rtd
                            (record-constructor
                             (make-record-constructor-descriptor rtd #f #f))
                            (record-predicate rtd))))
            (hashtable-set! tbl f e)
            e))))

  ;;; For generated code, which binds these once per functor at load.
  ;;; A bare functor gets a new closure each time.
  (define (compound-constructor f n)
    (if (typed-functor? f)
        (vector-ref (compound-type f n) 1)
        (case n
          ((1) (lambda (a) (%make-dyn1 a f)))
          ((2) (lambda (a b) (%make-dyn2 a b f)))
          ((3) (lambda (a b c) (%make-dyn3 a b c f)))
          ((4) (lambda (a b c d) (%make-dyn4 a b c d f)))
          ((5) (lambda (a b c d e) (%make-dyn5 a b c d e f)))
          ((6) (lambda (a b c d e g) (%make-dyn6 a b c d e g f)))
          ((7) (lambda (a b c d e g h) (%make-dyn7 a b c d e g h f)))
          ((8) (lambda (a b c d e g h i) (%make-dyn8 a b c d e g h i f)))
          (else (lambda (args) (%make-dyn* args f))))))

  (define (compound-predicate f n)
    (if (typed-functor? f)
        (vector-ref (compound-type f n) 2)
        (case n
          ((1) (lambda (v) (and (dyn1? v) (eq? (dyn1-functor v) f))))
          ((2) (lambda (v) (and (dyn2? v) (eq? (dyn2-functor v) f))))
          ((3) (lambda (v) (and (dyn3? v) (eq? (dyn3-functor v) f))))
          ((4) (lambda (v) (and (dyn4? v) (eq? (dyn4-functor v) f))))
          ((5) (lambda (v) (and (dyn5? v) (eq? (dyn5-functor v) f))))
          ((6) (lambda (v) (and (dyn6? v) (eq? (dyn6-functor v) f))))
          ((7) (lambda (v) (and (dyn7? v) (eq? (dyn7-functor v) f))))
          ((8) (lambda (v) (and (dyn8? v) (eq? (dyn8-functor v) f))))
          (else (lambda (v) (and (dyn*? v) (eq? (dyn*-functor v) f)))))))

  ;;; The entry of `f` in slot `k` if `f` is typed, else #f. The last
  ;;; functor is checked first, so a run of one typed functor does no
  ;;; hashing.
  (define (typed-entry f k)
    (cond ((eq? (vector-ref last-functors k) f) (vector-ref last-entries k))
          ((typed-functor? f) (compound-type f k))
          (else #f)))

  ;;; The constructors by functor, for code that builds terms outside a
  ;;; generated library. A typed functor costs at most one table lookup
  ;;; per term, a bare one none.
  (define (make-compound1 f a)
    (let ((e (typed-entry f 1)))
      (if e ((vector-ref e 1) a) (%make-dyn1 a f))))
  (define (make-compound2 f a b)
    (let ((e (typed-entry f 2)))
      (if e ((vector-ref e 1) a b) (%make-dyn2 a b f))))
  (define (make-compound3 f a b c)
    (let ((e (typed-entry f 3)))
      (if e ((vector-ref e 1) a b c) (%make-dyn3 a b c f))))
  (define (make-compound4 f a b c d)
    (let ((e (typed-entry f 4)))
      (if e ((vector-ref e 1) a b c d) (%make-dyn4 a b c d f))))
  (define (make-compound5 f a b c d e)
    (let ((t (typed-entry f 5)))
      (if t ((vector-ref t 1) a b c d e) (%make-dyn5 a b c d e f))))
  (define (make-compound6 f a b c d e g)
    (let ((t (typed-entry f 6)))
      (if t ((vector-ref t 1) a b c d e g) (%make-dyn6 a b c d e g f))))
  (define (make-compound7 f a b c d e g h)
    (let ((t (typed-entry f 7)))
      (if t ((vector-ref t 1) a b c d e g h) (%make-dyn7 a b c d e g h f))))
  (define (make-compound8 f a b c d e g h i)
    (let ((t (typed-entry f 8)))
      (if t ((vector-ref t 1) a b c d e g h i)
          (%make-dyn8 a b c d e g h i f))))
  ;;; Always a `compound*`, whatever the length (0 picks that slot).
  (define (make-compound* f args)
    (let ((e (typed-entry f 0)))
      (if e ((vector-ref e 1) args) (%make-dyn* args f))))

  ;;; Any compound record: a child of one of the parents. On Guile a
  ;;; parent check walks the child's ancestry, so it costs more than a
  ;;; sealed check; Chez checks a parent in about the same time.
  (define (compound? v)
    (or (compound2? v) (compound1? v) (compound3? v) (compound4? v)
        (compound5? v) (compound6? v) (compound7? v) (compound8? v)
        (compound*? v)))

  ;;; The functor: the name of the term's own type, or the field of a
  ;;; bare term.
  (define (compound-functor t)
    (let ((name (record-type-name (record-rtd t))))
      (if (eq? name dyn-name) (dyn-functor t) name)))

  (define (term? v) (or (pair? v) (compound? v)))

  (define (term-functor v)
    (if (pair? v) cons-functor (compound-functor v)))

  ;;; Number of arguments. Most frequent arities first.
  (define (term-arity t)
    (cond
      ((pair? t) 2)
      ((compound2? t) 2)
      ((compound1? t) 1)
      ((compound3? t) 3)
      ((compound4? t) 4)
      ((compound5? t) 5)
      ((compound6? t) 6)
      ((compound7? t) 7)
      ((compound8? t) 8)
      (else (vector-length (compound*-args t)))))

  ;;; Argument `i` (0-based), not dereferenced. No bounds check on a flat
  ;;; record: an index past the end reads the last field. The compiler
  ;;; only emits valid indexes.
  (define (term-arg t i)
    (cond
      ((pair? t) (if (eqv? i 0) (car t) (cdr t)))
      ((compound2? t) (if (eqv? i 0) (compound2-a1 t) (compound2-a2 t)))
      ((compound1? t) (compound1-a1 t))
      ((compound3? t)
       (case i ((0) (compound3-a1 t)) ((1) (compound3-a2 t))
         (else (compound3-a3 t))))
      ((compound4? t)
       (case i ((0) (compound4-a1 t)) ((1) (compound4-a2 t))
         ((2) (compound4-a3 t)) (else (compound4-a4 t))))
      ((compound5? t)
       (case i ((0) (compound5-a1 t)) ((1) (compound5-a2 t))
         ((2) (compound5-a3 t)) ((3) (compound5-a4 t))
         (else (compound5-a5 t))))
      ((compound6? t)
       (case i ((0) (compound6-a1 t)) ((1) (compound6-a2 t))
         ((2) (compound6-a3 t)) ((3) (compound6-a4 t))
         ((4) (compound6-a5 t)) (else (compound6-a6 t))))
      ((compound7? t)
       (case i ((0) (compound7-a1 t)) ((1) (compound7-a2 t))
         ((2) (compound7-a3 t)) ((3) (compound7-a4 t))
         ((4) (compound7-a5 t)) ((5) (compound7-a6 t))
         (else (compound7-a7 t))))
      ((compound8? t)
       (case i ((0) (compound8-a1 t)) ((1) (compound8-a2 t))
         ((2) (compound8-a3 t)) ((3) (compound8-a4 t))
         ((4) (compound8-a5 t)) ((5) (compound8-a6 t))
         ((6) (compound8-a7 t)) (else (compound8-a8 t))))
      (else (vector-ref (compound*-args t) i))))

  ;;; A fresh vector of the arguments. Allocates for every term: use
  ;;; `term-arity` / `term-arg` on hot paths.
  (define (term-args t)
    (let* ((n (term-arity t)) (v (make-vector n)))
      (do ((i 0 (+ i 1))) ((= i n) v)
        (vector-set! v i (term-arg t i)))))

  ;;; Build a term from a functor and a vector of arguments. The only
  ;;; generic constructor: it picks the one representation the arity
  ;;; allows.
  (define (make-term functor args)
    (let ((n (vector-length args)))
      (define (a i) (vector-ref args i))
      (if (and (= n 2) (eq? functor cons-functor))
          (cons (a 0) (a 1))
          (case n
            ((1) (make-compound1 functor (a 0)))
            ((2) (make-compound2 functor (a 0) (a 1)))
            ((3) (make-compound3 functor (a 0) (a 1) (a 2)))
            ((4) (make-compound4 functor (a 0) (a 1) (a 2) (a 3)))
            ((5) (make-compound5 functor (a 0) (a 1) (a 2) (a 3) (a 4)))
            ((6) (make-compound6 functor (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)))
            ((7) (make-compound7 functor (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
                                 (a 6)))
            ((8) (make-compound8 functor (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
                                 (a 6) (a 7)))
            ;; Above K, or nullary: a `compound*`. Only
            ;; `write_store_to_list` builds a nullary one, for a
            ;; nullary constraint: the reference builds a nullary
            ;; compound there (`VTerm t []`), not an atom, so this is
            ;; one too.
            (else (make-compound* functor args))))))

  ;;; The same functor over `(f arg)` for every argument, without an
  ;;; intermediate vector for a flat term. `f` is called left to right.
  ;;; The fast paths rebuild with the term's own functor, so they never
  ;;; turn a record into a pair: nothing builds a `prelude__.` record.
  (define (term-map f t)
    (cond
      ((pair? t) (let* ((h (f (car t))) (tl (f (cdr t)))) (cons h tl)))
      ((compound2? t)
       (let* ((x1 (f (compound2-a1 t))) (x2 (f (compound2-a2 t))))
         (make-compound2 (compound-functor t) x1 x2)))
      ((compound1? t) (make-compound1 (compound-functor t) (f (compound1-a1 t))))
      ((compound3? t)
       (let* ((x1 (f (compound3-a1 t))) (x2 (f (compound3-a2 t)))
              (x3 (f (compound3-a3 t))))
         (make-compound3 (compound-functor t) x1 x2 x3)))
      (else
       (let* ((n (term-arity t)) (v (make-vector n)))
         (do ((i 0 (+ i 1))) ((= i n))
           (vector-set! v i (f (term-arg t i))))
         (make-term (compound-functor t) v)))))

  ;;; `match-term` at a fixed arity, by functor: dereference, then a
  ;;; parent test and the functor. Generated libraries use the
  ;;; functor's own predicate instead (`compound-predicate`).
  (define (match-term1 v f)
    (let ((d (deref v))) (and (compound1? d) (eq? (compound-functor d) f))))
  (define (match-term2 v f)
    (let ((d (deref v))) (and (compound2? d) (eq? (compound-functor d) f))))
  (define (match-term3 v f)
    (let ((d (deref v))) (and (compound3? d) (eq? (compound-functor d) f))))
  (define (match-term4 v f)
    (let ((d (deref v))) (and (compound4? d) (eq? (compound-functor d) f))))
  (define (match-term5 v f)
    (let ((d (deref v))) (and (compound5? d) (eq? (compound-functor d) f))))
  (define (match-term6 v f)
    (let ((d (deref v))) (and (compound6? d) (eq? (compound-functor d) f))))
  (define (match-term7 v f)
    (let ((d (deref v))) (and (compound7? d) (eq? (compound-functor d) f))))
  (define (match-term8 v f)
    (let ((d (deref v))) (and (compound8? d) (eq? (compound-functor d) f))))

  ;;; Above K: the functor's predicate `p`, then the arity.
  (define (match-compound* v p n)
    (let ((d (deref v)))
      (and (p d) (= (vector-length (compound*-args d)) n))))

  ;;; Two compounds with the same functor and arity; #f when `d1` or
  ;;; `d2` is not a compound. That is one type comparison, plus the
  ;;; functor for bare terms and the length above K.
  (define (same-shape? d1 d2)
    (and (record? d1) (record? d2)
         (let ((rtd (record-rtd d1)))
           (and (eq? rtd (record-rtd d2))
                (compound? d1)
                (or (not (eq? (record-type-name rtd) dyn-name))
                    (eq? (dyn-functor d1) (dyn-functor d2)))
                (or (not (compound*? d1))
                    (= (vector-length (compound*-args d1))
                       (vector-length (compound*-args d2))))))))

  ;;; Atoms. An atom is a symbol, or `'()` for the nil atom.
  ;;; `atom->symbol` gives an atom's name as a symbol; `symbol->atom` is
  ;;; its inverse, and is what code that builds an atom from a name must
  ;;; use, so nil is never spelled as the symbol.
  (define (chr-atom? v) (or (symbol? v) (null? v)))
  (define (atom->symbol v) (if (null? v) nil-symbol v))
  (define (symbol->atom s) (if (eq? s nil-symbol) '() s))

  ;;; Dereferencing with path compression
  ;;;
  ;;; The compression write is skipped while a search trail is active.
  ;;; Trailing it would work (the Haskell runtime does), but it is not
  ;;; needed: a compression records nothing the walk could not recompute,
  ;;; and a branch that bound the variable underneath it is undone by the
  ;;; entry for that binding. Skipping is cheaper and loses only the
  ;;; shortening, so a long binding chain built inside a search is walked
  ;;; in full until the search exits.
  (define (deref v)
    (if (var? v)
        (let ((val (var-value v)))
          (if (eq? val *unbound*)
              v
              (let ((result (deref val)))
                (when (and (not (eq? result v)) (not (trail-active?)))
                  (var-value-set! v result))
                result)))
        v))

  ;;; Dereferencing without path compression.
  ;;;
  ;;; Only unifiable? uses this, and it must. That check's own writes
  ;;; are hypothetical and rolled back from a private trail, but a
  ;;; compression write made *through* one of them touches a different
  ;;; cell, is not on that trail, and would survive the rollback --
  ;;; leaving a variable bound to a value the check merely supposed.
  ;;; For W aliased to V: the check tentatively binds V to 1, then
  ;;; dereferences W, walks W -> V -> 1, and compresses W to 1.
  ;;; Restoring V then leaves W bound to 1 and the alias destroyed,
  ;;; whatever the check answered.
  (define (deref/no-compress v)
    (if (var? v)
        (let ((val (var-value v)))
          (if (eq? val *unbound*)
              v
              (deref/no-compress val)))
        v))

  ;;; Unification (tell semantics, Prolog =)
  ;;;
  ;;; Every cell write is recorded on the search trail, if one is active:
  ;;; the driver unwinds a branch by replaying them, and the observers it
  ;;; emits are dropped there rather than drained.
  (define (unify v1 v2)
    (let ((observers '()))
      (define (emit! obs)
        (set! observers (append obs observers)))
      (let ((result (unify* (deref v1) (deref v2) emit!)))
        (values result observers))))

  (define (unify* d1 d2 emit!)
    (cond
      ((and (var? d1) (var? d2) (eq? d1 d2)) #t)
      ((and (var? d1) (var? d2))
       (let ((obs1 (var-observers d1))
             (obs2 (var-observers d2)))
         (trail-value! d1)
         (trail-observers! d1)
         (trail-observers! d2)
         (var-value-set! d1 d2)
         (var-observers-set! d1 '())
         (var-observers-set! d2 (append obs1 obs2))
         (emit! obs1)
         #t))
      ((var? d1)
       (let ((obs (var-observers d1)))
         (trail-value! d1)
         (trail-observers! d1)
         (var-value-set! d1 d2)
         (var-observers-set! d1 '())
         ;; Move X's observers onto the unbound vars now reachable
         ;; through X, like Haskell's `unify'` (Var.hs). Otherwise after
         ;; X = g(A), a later A = 1 wakes nothing.
         (for-each (lambda (oid) (add-observer! oid d2)) obs)
         (emit! obs)
         #t))
      ((var? d2)
       (unify* d2 d1 emit!))
      ((and (integer? d1) (integer? d2))
       (eqv? d1 d2))
      ((and (symbol? d1) (symbol? d2))
       (eq? d1 d2))
      ((and (boolean? d1) (boolean? d2))
       (eq? d1 d2))
      ((and (string? d1) (string? d2))
       (string=? d1 d2))
      ((and (null? d1) (null? d2)) #t)
      ((and (pair? d1) (pair? d2))
       (let-values (((ok obs) (unify (car d1) (car d2))))
         (emit! obs)
         (and ok
              (let-values (((ok obs) (unify (cdr d1) (cdr d2))))
                (emit! obs)
                ok))))
      ((same-shape? d1 d2)
       (unify-args d1 d2 0 (term-arity d1) emit!))
      (else #f)))

  (define (unify-args t1 t2 i n emit!)
    (if (= i n)
        #t
        (let-values (((ok obs) (unify (term-arg t1 i) (term-arg t2 i))))
          (emit! obs)
          (if ok
              (unify-args t1 t2 (+ i 1) n emit!)
              #f))))

  ;;; Unifiability check: does unify succeed, without mutating any
  ;;; bindings? Mirrors unify*/unify-args but uses a trail list to roll
  ;;; back every mutation before returning. Observers are never touched.
  ;;;
  ;;; The walk uses deref/no-compress rather than deref, so that the
  ;;; trail is the only writer; see there.
  (define (unifiable? v1 v2)
    (let ((trail '()))
      (define (trail! v)
        ;; Record the current var-value so it can be restored later.
        (set! trail (cons (cons v (var-value v)) trail)))
      (define (uni a b)
        (uni* (deref/no-compress a) (deref/no-compress b)))
      (define (uni* d1 d2)
        (cond
          ((and (var? d1) (var? d2) (eq? d1 d2)) #t)
          ((var? d1)
           (trail! d1)
           (var-value-set! d1 d2)
           #t)
          ((var? d2)
           (trail! d2)
           (var-value-set! d2 d1)
           #t)
          ((and (integer? d1) (integer? d2)) (eqv? d1 d2))
          ((and (symbol? d1) (symbol? d2)) (eq? d1 d2))
          ((and (boolean? d1) (boolean? d2)) (eq? d1 d2))
          ((and (string? d1) (string? d2)) (string=? d1 d2))
          ((and (null? d1) (null? d2)) #t)
          ((and (pair? d1) (pair? d2))
           (and (uni (car d1) (car d2)) (uni (cdr d1) (cdr d2))))
          ((same-shape? d1 d2)
           (uni-args d1 d2 0 (term-arity d1)))
          (else #f)))
      (define (uni-args t1 t2 i n)
        (if (= i n)
            #t
            (if (uni (term-arg t1 i) (term-arg t2 i))
                (uni-args t1 t2 (+ i 1) n)
                #f)))
      (let ((result (uni v1 v2)))
        ;; Restore every trailed var to its original value. Entries are
        ;; prepended newest-first, so walking front-to-back restores each
        ;; cell to its oldest captured state.
        (for-each (lambda (entry)
                    (var-value-set! (car entry) (cdr entry)))
                  trail)
        result)))

  ;;; Equality (ask semantics, Prolog ==)
  (define (equal?/chr v1 v2)
    (equal* (deref v1) (deref v2)))

  (define (equal* d1 d2)
    (cond
      ((and (var? d1) (var? d2)) (eq? d1 d2))
      ((or (var? d1) (var? d2)) #f)
      ;; Numeric equality. eqv? distinguishes exact and inexact, so an
      ;; integer is never equal to a flonum even when their values
      ;; coincide — matching the Haskell side which keeps VInt and
      ;; VFloat separate.
      ((and (number? d1) (number? d2)) (eqv? d1 d2))
      ((and (symbol? d1) (symbol? d2)) (eq? d1 d2))
      ((and (boolean? d1) (boolean? d2)) (eq? d1 d2))
      ((and (string? d1) (string? d2)) (string=? d1 d2))
      ((and (null? d1) (null? d2)) #t)
      ((and (pair? d1) (pair? d2))
       (and (equal?/chr (car d1) (car d2))
            (equal?/chr (cdr d1) (cdr d2))))
      ((same-shape? d1 d2)
       (equal-args d1 d2 0 (term-arity d1)))
      (else #f)))

  (define (equal-args t1 t2 i n)
    (if (= i n)
        #t
        (if (equal?/chr (term-arg t1 i) (term-arg t2 i))
            (equal-args t1 t2 (+ i 1) n)
            #f)))

  ;;; Term operations
  ;; 0-arity compounds collapse to symbols at the runtime layer
  ;; (matching the Haskell side's VAtom canonical form), so a symbol
  ;; matches when arity is 0 and its name equals functor.
  (define (match-term v functor arity)
    (let ((d (deref v)))
      (cond
        ((pair? d) (and (= arity 2) (eq? functor cons-functor)))
        ((null? d) (and (= arity 0) (eq? functor nil-symbol)))
        ((symbol? d) (and (= arity 0) (eq? d functor)))
        ((compound? d)
         (and (eq? (compound-functor d) functor)
              (= (term-arity d) arity)))
        (else #f))))

  (define (get-arg v idx)
    (term-arg (deref v) idx))

  ;;; Observer management
  ;; Register an observer on every unbound variable reachable from a
  ;; value: a bare unbound variable directly, and every variable nested
  ;; inside a compound term's arguments (e.g. the X in pair(X, 1) or
  ;; [X, X]) by recursion. Without the recursion a constraint stored
  ;; with such an argument would never be reactivated when the nested
  ;; variable is later bound, missing an omega-r Reactivate step.
  (define (add-observer! suspension-id v)
    (let ((d (deref v)))
      (cond
        ((and (var? d) (eq? (var-value d) *unbound*))
         (trail-observers! d)
         (var-observers-set! d (cons suspension-id (var-observers d))))
        ((pair? d)
         (add-observer! suspension-id (car d))
         (add-observer! suspension-id (cdr d)))
        ((compound? d)
         (add-observer-args! suspension-id d 0 (term-arity d))))))

  (define (add-observer-args! suspension-id t i n)
    (when (< i n)
      (add-observer! suspension-id (term-arg t i))
      (add-observer-args! suspension-id t (+ i 1) n)))

  ;;; Ground keys
  ;;;
  ;;; The key of a constraint argument, for the store's per-argument
  ;;; indexes (the paper's Indexing optimization; see store.sls). It
  ;;; mirrors `groundKey`/`addObserverAndKey` in
  ;;; src/YCHR/Internal/Runtime/Var.hs.
  ;;;
  ;;; A key is ordinary Scheme data, compared with `equal?` (which uses
  ;;; `eqv?` on numbers, so an exact 1 and an inexact 1.0 stay
  ;;; distinct, exactly as `equal?/chr` keeps them):
  ;;;
  ;;;   (num . n)       a number, with `number-key` normalization below
  ;;;   (atom . s)      a symbol; nil is the symbol `prelude__[]`
  ;;;   (text . s)      a string
  ;;;   (bool . b)      a boolean
  ;;;   (term f k ...)  a compound: functor plus one key per argument
  ;;;
  ;;; `#f` means "not ground": an unbound variable, a compound holding
  ;;; one, or any value `equal?/chr` never equates with anything. Such
  ;;; an argument goes to its position's non-ground fallback set, which
  ;;; every lookup for that position scans, so the index may only ever
  ;;; narrow a lookup to a superset of the matches. Key equality is
  ;;; deliberately never finer than `equal?/chr`: `number-key` collapses
  ;;; 0.0 and -0.0 (which `eqv?` distinguishes) and every NaN, which
  ;;; only ever yields extra candidates for the per-candidate check to
  ;;; reject.
  (define (ground-key v) (value-key v #f))

  ;;; One traversal with the two jobs an indexed constraint argument
  ;;; needs: register `suspension-id` as an observer on every unbound
  ;;; variable reachable from `v` — exactly what `add-observer!` does —
  ;;; and return `v`'s ground key. They share a traversal because they
  ;;; inspect the same term the same way; a store that indexes a
  ;;; position would otherwise walk each of its arguments twice.
  ;;;
  ;;; Meeting an unbound variable does not stop the walk — the variables
  ;;; behind it still need observing — it only discards the key, so the
  ;;; whole argument is always visited. An observer id of `#f` (never a
  ;;; valid suspension) means "compute the key only", which is what
  ;;; `ground-key` and the store's on-demand backlog pass need.
  (define (add-observer-and-key suspension-id v)
    (value-key v suspension-id))

  ;;; The normalized key payload of a number. The `flonum?` guard is what
  ;;; makes the test total: `nan?` raises on a non-real complex, which
  ;;; `equal?/chr` would have compared with `eqv?` quite happily, so an
  ;;; unguarded test could make a store that used to work raise once its
  ;;; type crossed the index threshold. `zero?` is total on every number,
  ;;; and an exact non-integer (a rational, which only a
  ;;; wider-than-Haskell host call can produce) passes through and keeps
  ;;; `eqv?`'s exact/inexact distinction because `equal?` on numbers is
  ;;; `eqv?`.
  (define (number-key x)
    (cond ((and (flonum? x) (nan? x)) 'nan)
          ((zero? x) 0)
          (else x)))

  (define (value-key v oid)
    (let ((d (deref v)))
      (cond
        ((and (var? d) (eq? (var-value d) *unbound*))
         (when oid
           (trail-observers! d)
           (var-observers-set! d (cons oid (var-observers d))))
         #f)
        ((number? d) (cons 'num (number-key d)))
        ((symbol? d) (cons 'atom d))
        ((null? d) (cons 'atom nil-symbol))
        ((string? d) (cons 'text d))
        ((boolean? d) (cons 'bool d))
        ((pair? d)
         ;; Same key shape as the record form, so the key does not
         ;; depend on how the cell is stored.
         (let* ((kh (value-key (car d) oid))
                (kt (value-key (cdr d) oid)))
           (and kh kt (list 'term cons-functor kh kt))))
        ((term? d)
         (let ((n (term-arity d)))
           (let loop ((i 0) (keys '()) (all-keys? #t))
             (if (= i n)
                 (and all-keys?
                      (cons 'term (cons (term-functor d) (reverse keys))))
                 (let ((k (value-key (term-arg d i) oid)))
                   (loop (+ i 1) (cons k keys) (and all-keys? (if k #t #f))))))))
        (else #f))))

  ;;; `(ground? t)`: no variable occurs in `t`, bound or not. Unlike
  ;;; `%ground?` (the host call behind `ground/1`) it does not
  ;;; dereference: a bound variable counts as not ground, because a
  ;;; ground library from `ychr scheme-types --ground` would not
  ;;; dereference it either. Walks pairs and compounds.
  (define (ground? t)
    (cond ((var? t) #f)
          ((pair? t) (and (ground? (car t)) (ground? (cdr t))))
          ((compound? t)
           (let ((n (term-arity t)))
             (let loop ((i 0))
               (or (= i n)
                   (and (ground? (term-arg t i)) (loop (+ i 1)))))))
          (else #t)))

  ;;; Var ID extraction
  (define (get-var-id v)
    (let ((d (deref v)))
      (if (and (var? d) (eq? (var-value d) *unbound*))
          (var-id d)
          #f)))
)
