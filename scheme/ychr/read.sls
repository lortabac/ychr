;;;; Term reader for the CHR surface syntax.
;;;;
;;;; The dual of (ychr pretty): `parse-term` reads one term out of a
;;;; string and builds the runtime value it denotes. It mirrors the
;;;; Haskell reference, `YCHR.Internal.Meta.read_term_from_string`:
;;;; the Pratt parser of `YCHR.Internal.PExpr` driven by the session's
;;;; operator table (`SessionEnv.opTable`, carried here as
;;;; `session-op-table`), followed by `termToValue`'s conversion.
;;;;
;;;; The table is the program's own — the built-ins merged with every
;;;; operator the loaded modules declare or import — so a string read at
;;;; run time can spell any operator the program can, exactly as the
;;;; goal parser can. A hand-built session carries `(ychr optable)`'s
;;;; `builtin-op-table`, the counterpart of the `builtinOps`
;;;; `initSessionEnv` gives the reference's hand-built sessions.
;;;;
;;;; The conversion mirrors `convertTerm` + `termToValue`:
;;;;
;;;;   * a named variable is one fresh logical variable per distinct
;;;;     spelling, shared between its occurrences;
;;;;   * `_` is a fresh logical variable per occurrence;
;;;;   * `true` / `false` (and the qualified `prelude:true` /
;;;;     `prelude:false`) are the native booleans, not atoms;
;;;;   * `fun name/arity` is a first-class function reference: the name is
;;;;     resolved against the session's callables table and the shape is
;;;;     rewritten to the canonical `/`(flat-name, arity) closure, exactly
;;;;     as the reference reader does (see the resolution section below);
;;;;   * a 0-arity name is an atom; a compound with arguments is a term;
;;;;   * a `module:name` is kept in its colon spelling, as the
;;;;     reference's `flattenName` does — never the mangled `module__name`
;;;;     the compiler emits — so a parsed qualified functor prints the
;;;;     same way on both backends;
;;;;   * list syntax keeps the `.` / `[]` functors the parser builds,
;;;;     not the prelude's canonicalized `prelude__.` / `prelude__[]`.
(library (ychr read)
  (export parse-term resolve-funref-identity)
  (import (rnrs)
          (rnrs unicode)
          (ychr session)
          (ychr var)
          (ychr optable))

  ;;; ---------------------------------------------------------------------
  ;;; Character classes
  ;;;
  ;;; `YCHR.Internal.PExpr` uses parsec's `lower`, `upper` and `alphaNum`,
  ;;; which are Unicode-aware: `isLower` / `isUpper` are exactly the Ll /
  ;;; Lu general categories, and `isAlphaNum` also covers Nl/No (so
  ;;; `a²` and `aⅧ` are identifier characters). The predicates below
  ;;; mirror that, as `pretty.sls` does for atom quoting.
  ;;; ---------------------------------------------------------------------

  (define (lower-letter? c) (eq? (char-general-category c) 'Ll))
  (define (upper-letter? c) (eq? (char-general-category c) 'Lu))
  (define (alpha-num? c)
    (memq (char-general-category c) '(Lu Ll Lt Lm Lo Nd Nl No)))

  ;; `parsec`'s `digit`: ASCII 0-9 only, unlike `char-numeric?`.
  (define (decimal-digit? c) (and (char<=? #\0 c) (char<=? c #\9)))

  ;; `Data.Char.isSpace`: the ASCII space characters plus the Zs
  ;; category. Deliberately not `char-whitespace?`, which is
  ;; implementation-defined past that (Guile adds U+2028/U+2029, Chez
  ;; U+0085), so the same input would parse differently on the two
  ;; implementations where the reference rejects it.
  (define (space-char? c)
    (or (memv c (list #\space #\tab #\newline #\return #\page #\vtab))
        (eq? (char-general-category c) 'Zs)))

  (define (char-in-string? c str)
    (let loop ((i 0))
      (cond ((>= i (string-length str)) #f)
            ((char=? c (string-ref str i)) #t)
            (else (loop (+ i 1))))))

  ;; True when `needle` occurs in `s` (no portable `string-contains`).
  (define (string-has? s needle)
    (let ((n (string-length s)) (m (string-length needle)))
      (let loop ((i 0))
        (cond ((> (+ i m) n) #f)
              ((string=? needle (substring s i (+ i m))) #t)
              (else (loop (+ i 1)))))))

  ;;; ---------------------------------------------------------------------
  ;;; Operator-table helpers
  ;;;
  ;;; The table itself — the built-in transcription and the
  ;;; `(fixity type name)` entry shape — lives in `(ychr optable)`.
  ;;; Every parser procedure below takes a table as its first argument
  ;;; and consults it through `op-lookup`, `op-table-infix`,
  ;;; `op-table-prefix` and `op-table-word`, mirroring the `OpTable ->`
  ;;; parameter threaded through `YCHR.Internal.PExpr`.
  ;;; ---------------------------------------------------------------------

  ;; Maximum fixity allowed for an operator's left argument: an `y`
  ;; position allows equal fixity, an `x` position requires strictly
  ;; lower (`leftMax` in YCHR.Internal.PExpr).
  (define (left-max ty fix)
    (if (or (eq? ty 'yfx) (eq? ty 'yf)) fix (- fix 1)))

  ;;; ---------------------------------------------------------------------
  ;;; Lexical helpers
  ;;;
  ;;; Every token parser consumes trailing `sc` (whitespace and `%` line
  ;;; comments) and returns an index at the next token, so callers never
  ;;; have to skip sc themselves.
  ;;; ---------------------------------------------------------------------

  ;; `sc` from YCHR.Internal.PExpr: whitespace, plus `%` line comments.
  (define (skip-sc s i)
    (let ((n (string-length s)))
      (let loop ((i i))
        (cond
          ((>= i n) i)
          ((space-char? (string-ref s i)) (loop (+ i 1)))
          ((char=? (string-ref s i) #\%)
           ;; `skipLineComment`: stop before the newline; the next
           ;; iteration consumes it as whitespace.
           (let line ((j (+ i 1)))
             (if (or (>= j n) (char=? (string-ref s j) #\newline))
                 (loop j)
                 (line (+ j 1)))))
          (else i)))))

  (define (starts-with? s i text)
    (and (<= (+ i (string-length text)) (string-length s))
         (string=? text (substring s i (+ i (string-length text))))))

  ;; True when position I is at end of input or not inside an identifier
  ;; (`notFollowedBy (alphaNum <|> char '_')`).
  (define (word-boundary? s i)
    (or (>= i (string-length s))
        (not (or (alpha-num? (string-ref s i))
                 (char=? (string-ref s i) #\_)))))

  (define (unescape c)
    (cond ((char=? c #\n) #\newline)
          ((char=? c #\t) #\tab)
          (else c)))

  ;; `identifierP`: a lowercase identifier, rejecting `__`.
  (define (parse-identifier s i)
    (let ((n (string-length s)))
      (if (and (< i n) (lower-letter? (string-ref s i)))
          (let loop ((j (+ i 1)))
            (if (and (< j n)
                     (or (alpha-num? (string-ref s j))
                         (char=? (string-ref s j) #\_)))
                (loop (+ j 1))
                (let ((t (substring s i j)))
                  (and (not (string-has? t "__"))
                       (cons t (skip-sc s j))))))
          #f)))

  ;; `varOrWildcardP`: an uppercase- or underscore-initial variable, with
  ;; the lone `_` as the wildcard. Unlike an atom, a variable name may
  ;; contain `__` (`__Foo` is a variable).
  (define (parse-var-or-wildcard s i)
    (let ((n (string-length s)))
      (if (>= i n)
          #f
          (let ((c (string-ref s i)))
            (if (or (upper-letter? c) (char=? c #\_))
                (let loop ((j (+ i 1)))
                  (if (and (< j n)
                           (or (alpha-num? (string-ref s j))
                               (char=? (string-ref s j) #\_)))
                      (loop (+ j 1))
                      (let ((t (substring s i j)))
                        (cons (if (and (char=? c #\_) (= j (+ i 1)))
                                  (vector 'wildcard)
                                  (vector 'var t))
                              (skip-sc s j)))))
                #f)))))

  ;; `numberP`: an optional sign, then a float (`whole.frac`, requiring
  ;; digits on both sides of the dot) or an integer. ASCII digits only.
  (define (parse-number s i)
    (let* ((n (string-length s))
           (neg (and (< i n) (char=? (string-ref s i) #\-)))
           (start (if neg (+ i 1) i)))
      (let digits ((j start))
        (if (and (< j n) (decimal-digit? (string-ref s j)))
            (digits (+ j 1))
            (if (= j start)
                #f
                (if (and (< (+ j 1) n)
                         (char=? (string-ref s j) #\.)
                         (decimal-digit? (string-ref s (+ j 1))))
                    (let frac ((k (+ j 1)))
                      (if (and (< k n) (decimal-digit? (string-ref s k)))
                          (frac (+ k 1))
                          (let* ((text (string-append (substring s start j)
                                                      "."
                                                      (substring s (+ j 1) k)))
                                 (v (string->number text)))
                            (cons (vector 'float (if neg (- v) v))
                                  (skip-sc s k)))))
                    (let ((v (string->number (substring s start j))))
                      (cons (vector 'int (if neg (- v) v))
                            (skip-sc s j)))))))))

  ;; `stringP`: a double-quoted string literal.
  (define (parse-string-literal s i)
    (let ((n (string-length s)))
      (if (and (< i n) (char=? (string-ref s i) #\"))
          (let loop ((j (+ i 1)) (acc '()))
            (cond
              ((>= j n) #f)
              ((char=? (string-ref s j) #\")
               (cons (vector 'text (list->string (reverse acc)))
                     (skip-sc s (+ j 1))))
              ((char=? (string-ref s j) #\\)
               (and (< (+ j 1) n)
                    (loop (+ j 2) (cons (unescape (string-ref s (+ j 1))) acc))))
              (else (loop (+ j 1) (cons (string-ref s j) acc)))))
          #f)))

  ;; `quotedAtomP`: a single-quoted atom, with `''` for an embedded
  ;; quote. Rejects `__` and the reserved `%%u` escape marker.
  (define (parse-quoted-atom s i)
    (let ((n (string-length s)))
      (if (and (< i n) (char=? (string-ref s i) #\'))
          (let loop ((j (+ i 1)) (acc '()))
            (cond
              ((>= j n) #f)
              ((char=? (string-ref s j) #\')
               (if (and (< (+ j 1) n) (char=? (string-ref s (+ j 1)) #\'))
                   (loop (+ j 2) (cons #\' acc))
                   (let ((t (list->string (reverse acc))))
                     (and (not (string-has? t "__"))
                          (not (string-has? t "%%u"))
                          (cons (vector 'atom t) (skip-sc s (+ j 1)))))))
              ((char=? (string-ref s j) #\\)
               (and (< (+ j 1) n)
                    (loop (+ j 2) (cons (unescape (string-ref s (+ j 1))) acc))))
              (else (loop (+ j 1) (cons (string-ref s j) acc)))))
          #f)))

  ;; `anyOpToken`: the longest symbol-operator run (the whole run must be
  ;; an operator, so `=<` — not in the table — is unknown rather than
  ;; `=` followed by `<`), a single `,`/`|`/`;`, or a word operator.
  (define (parse-op-token ops s i)
    (let ((n (string-length s)))
      (if (>= i n)
          #f
          (let ((c (string-ref s i)))
            (cond
              ((char-in-string? c symbol-chars)
               (let loop ((j i))
                 (if (and (< j n) (char-in-string? (string-ref s j) symbol-chars))
                     (loop (+ j 1))
                     (let ((t (substring s i j)))
                       (and (or (op-lookup t (op-table-infix ops))
                                (op-lookup t (op-table-prefix ops)))
                            (cons t (skip-sc s j)))))))
              ((char-in-string? c ",|;")
               (let ((t (string c)))
                 (and (or (op-lookup t (op-table-infix ops))
                          (op-lookup t (op-table-prefix ops)))
                      (cons t (skip-sc s (+ i 1))))))
              ((lower-letter? c)
               (let loop ((j (+ i 1)))
                 (if (and (< j n)
                          (or (alpha-num? (string-ref s j))
                              (char=? (string-ref s j) #\_)))
                     (loop (+ j 1))
                     (let ((t (substring s i j)))
                       (and (member t (op-table-word ops))
                            (cons t (skip-sc s j)))))))
              (else #f))))))

  ;;; ---------------------------------------------------------------------
  ;;; Term parser
  ;;;
  ;;; Nodes are tagged vectors: #(var name), #(wildcard), #(int n),
  ;;; #(float x), #(text s), #(atom name), #(compound name (node ...)).
  ;;; Every parser threads the operator table in scope and a string
  ;;; index, and returns a pair (node . next-index), or #f when the input
  ;;; does not parse; the index-based state is what makes the parser's
  ;;; `try` alternatives a saved-index retry.
  ;;; ---------------------------------------------------------------------

  ;; `atomP`: an unquoted identifier that is not a prefix word operator
  ;; (those are handled by the Pratt parser, or as `name(...)` functors),
  ;; or a quoted atom.
  (define (parse-atom ops s i)
    (or (parse-quoted-atom s i)
        (let ((id (parse-identifier s i)))
          (and id
               (let ((t (car id)))
                 (and (not (and (member t (op-table-word ops))
                                (op-lookup t (op-table-prefix ops))))
                      (cons (vector 'atom t) (cdr id))))))))

  ;; `sepBy` over `,` at argument precedence: zero or more terms. Returns
  ;; (ok elems next-index). An element that does not parse stops the list
  ;; — which is how zero arguments and the `[a, b | T]` tail are read —
  ;; but a comma left dangling with no element after it is a parse
  ;; failure (`parsec`'s `many` propagates a failure that consumed
  ;; input), so `f(a,)` is rejected rather than read as `f(a)`.
  (define (parse-args ops s i)
    (let loop ((i i) (acc '()) (no-dangling-comma #t))
      (let ((t (parse-term-at ops s i max-arg-prec)))
        (if (not t)
            (values no-dangling-comma (reverse acc) i)
            (let ((k (cdr t)))
              (if (and (< k (string-length s))
                       (char=? (string-ref s k) #\,))
                  (loop (skip-sc s (+ k 1)) (cons (car t) acc) #f)
                  (values #t (reverse (cons (car t) acc)) k)))))))

  ;; The argument list and closing `)` of a compound, starting after the
  ;; `(`.
  (define (parse-compound-tail ops s name i)
    (let-values (((ok args k) (parse-args ops s i)))
      (if (and ok
               (< k (string-length s))
               (char=? (string-ref s k) #\)))
          (cons (vector 'compound name args) (skip-sc s (+ k 1)))
          #f)))

  ;; `listTermP`: `[a, b | T]`, desugared to right-nested `.` compounds
  ;; terminated by the atom `[]`.
  (define (parse-list ops s i)
    (let ((n (string-length s)))
      (if (and (< i n) (char=? (string-ref s i) #\[))
          (let-values (((ok elems k) (parse-args ops s (skip-sc s (+ i 1)))))
            (cond
              ((not ok) #f)
              ((and (< k n) (char=? (string-ref s k) #\|))
               (let ((tail (parse-term-at ops s (skip-sc s (+ k 1)) max-arg-prec)))
                 (and tail
                      (let ((k2 (cdr tail)))
                        (and (< k2 n)
                             (char=? (string-ref s k2) #\])
                             (cons (build-list elems (car tail))
                                   (skip-sc s (+ k2 1))))))))
              ((and (< k n) (char=? (string-ref s k) #\]))
               (cons (build-list elems (vector 'atom "[]"))
                     (skip-sc s (+ k 1))))
              (else #f)))
          #f)))

  (define (build-list elems tail-node)
    (fold-right (lambda (h acc) (vector 'compound "." (list h acc)))
                tail-node
                elems))

  ;; `lambdaP`: `fun(X, Y) -> body end`. The whole production
  ;; backtracks, so `fun(a)` without the arrow still parses as the
  ;; compound `fun(a)`.
  (define (parse-lambda ops s i)
    (and (starts-with? s i "fun")
         (word-boundary? s (+ i 3))
         (let ((j (skip-sc s (+ i 3))))
           (and (< j (string-length s))
                (char=? (string-ref s j) #\()
                (let-values (((params-ok params k)
                              (parse-args ops s (skip-sc s (+ j 1)))))
                  (and params-ok
                       (< k (string-length s))
                       (char=? (string-ref s k) #\))
                       (let ((m (skip-sc s (+ k 1))))
                         (and (starts-with? s m "->")
                              (let ((body (parse-term-at ops s (skip-sc s (+ m 2)) max-prec)))
                                (and body
                                     (let ((e (skip-sc s (cdr body))))
                                       (and (starts-with? s e "end")
                                            (word-boundary? s (+ e 3))
                                            (cons (vector 'compound "->"
                                                          (list (vector 'compound "fun" params)
                                                                (car body)))
                                                  (skip-sc s (+ e 3)))))))))))))))

  ;; `parens`: a parenthesised term at top precedence.
  (define (parse-parens ops s i)
    (let ((n (string-length s)))
      (if (and (< i n) (char=? (string-ref s i) #\())
          (let ((t (parse-term-at ops s (skip-sc s (+ i 1)) max-prec)))
            (and t
                 (let ((k (cdr t)))
                   (and (< k n)
                        (char=? (string-ref s k) #\))
                        (cons (car t) (skip-sc s (+ k 1)))))))
          #f)))

  ;; A prefix word operator used as a functor: `chr_constraint(x)`.
  (define (parse-prefix-word-functor ops s i)
    (let ((id (parse-identifier s i)))
      (and id
           (let ((t (car id)))
             (and (member t (op-table-word ops))
                  (op-lookup t (op-table-prefix ops))
                  (let ((k (cdr id)))
                    (and (< k (string-length s))
                         (char=? (string-ref s k) #\()
                         (parse-compound-tail ops s t (skip-sc s (+ k 1))))))))))

  ;; `atomOrCompoundP`: an atom, optionally followed by `(args)`.
  (define (parse-atom-or-compound ops s i)
    (or (parse-prefix-word-functor ops s i)
        (let ((a (parse-atom ops s i)))
          (and a
               (let ((k (cdr a)))
                 (if (and (< k (string-length s))
                          (char=? (string-ref s k) #\())
                     (parse-compound-tail ops s (vector-ref (car a) 1)
                                          (skip-sc s (+ k 1)))
                     a))))))

  ;; `atomicTermP`, in the reference's order.
  (define (parse-atomic ops s i)
    (or (parse-var-or-wildcard s i)
        (parse-number s i)
        (parse-string-literal s i)
        (parse-list ops s i)
        (parse-lambda ops s i)
        (parse-parens ops s i)
        (parse-atom-or-compound ops s i)))

  ;; `nudP`: an atomic term, or a prefix operator and its operand.
  ;; Returns (node fixity next-index) or #f.
  (define (parse-nud ops s i max-fix)
    (let ((atomic (parse-atomic ops s i)))
      (if atomic
          (list (car atomic) 0 (cdr atomic))
          (let ((op (parse-op-token ops s i)))
            (and op
                 (let ((entry (op-lookup (car op) (op-table-prefix ops))))
                   (and entry
                        (<= (car entry) max-fix)
                        (let* ((fix (car entry))
                               (ty (cadr entry))
                               (operand-max (if (eq? ty 'fy) fix (- fix 1)))
                               (operand (parse-term-at ops s (cdr op) operand-max)))
                          (and operand
                               (list (vector 'compound (car op) (list (car operand)))
                                     fix
                                     (cdr operand)))))))))))

  ;; `ledLoop`: consume infix (and, generically, postfix) operators whose
  ;; fixity is within range and whose left-position constraint the
  ;; current left-hand side satisfies. Returns (node . next-index).
  (define (parse-led-loop ops s node node-fix i max-fix)
    (let ((op (parse-op-token ops s i)))
      (if (not op)
          (cons node i)
          (let ((entry (op-lookup (car op) (op-table-infix ops))))
            (if (and entry
                     (<= (car entry) max-fix)
                     (<= node-fix (left-max (cadr entry) (car entry))))
                (let ((fix (car entry)) (ty (cadr entry)))
                  (if (or (eq? ty 'xf) (eq? ty 'yf))
                      (parse-led-loop ops s
                                      (vector 'compound (car op) (list node))
                                      fix
                                      (cdr op)
                                      max-fix)
                      (let ((rhs (parse-term-at ops s
                                                (cdr op)
                                                (if (eq? ty 'xfy) fix (- fix 1)))))
                        (and rhs
                             (parse-led-loop ops s
                                             (vector 'compound (car op)
                                                     (list node (car rhs)))
                                             fix
                                             (cdr rhs)
                                             max-fix)))))
                (cons node i))))))

  (define (parse-term-at ops s i max-fix)
    (let ((nud (parse-nud ops s i max-fix)))
      (and nud
           (parse-led-loop ops s (car nud) (cadr nud) (caddr nud) max-fix))))

  ;;; ---------------------------------------------------------------------
  ;;; Conversion to runtime values
  ;;;
  ;;; Mirrors `convertTerm` (which turns a `PExpr` into a `Term`,
  ;;; intercepting `module:name`) followed by `termToValue`.
  ;;; ---------------------------------------------------------------------

  ;; A `Term` name is (module . base), the module being #f when
  ;; unqualified — the same split `Types.Name` carries.
  (define (flatten-name name)
    (if (car name)
        (string-append (car name) ":" (cdr name))
        (cdr name)))

  ;; `hostBool`: the two prelude booleans, in both the bare and the
  ;; qualified spelling.
  (define (name->value name)
    (let ((m (car name)) (n (cdr name)))
      (cond
        ((and (not m) (string=? n "true")) #t)
        ((and (not m) (string=? n "false")) #f)
        ((and m (string=? m "prelude") (string=? n "true")) #t)
        ((and m (string=? m "prelude") (string=? n "false")) #f)
        (m (string->symbol (flatten-name name)))
        (else (string->symbol n)))))

  ;; A name applied to converted arguments: 0-arity collapses to an atom
  ;; (or a native boolean), otherwise a compound term.
  (define (apply-name name args)
    (if (null? args)
        (name->value name)
        (make-term (string->symbol (flatten-name name)) (list->vector args))))

  (define (node->value session vars node)
    (let ((kind (vector-ref node 0)))
      (cond
        ((eq? kind 'var)
         (let* ((name (vector-ref node 1))
                (existing (hashtable-ref vars name #f)))
           (or existing
               (let ((v (make-var session)))
                 (hashtable-set! vars name v)
                 v))))
        ((eq? kind 'wildcard) (make-var session))
        ((eq? kind 'int) (vector-ref node 1))
        ((eq? kind 'float) (vector-ref node 1))
        ((eq? kind 'text) (vector-ref node 1))
        ((eq? kind 'atom)
         (apply-name (cons #f (vector-ref node 1)) '()))
        ((eq? kind 'compound)
         (let ((name (vector-ref node 1))
               (args (vector-ref node 2)))
           ;; `convertTerm` intercepts `module:name` (both the 0-arity
           ;; atom and the compound form) before the generic fallback.
           (if (and (string=? name ":")
                    (= (length args) 2)
                    (eq? (vector-ref (car args) 0) 'atom))
               (let ((m (vector-ref (car args) 1))
                     (second (cadr args)))
                 (cond
                   ((eq? (vector-ref second 0) 'atom)
                    (apply-name (cons m (vector-ref second 1)) '()))
                   ((eq? (vector-ref second 0) 'compound)
                    (apply-name (cons m (vector-ref second 1))
                                (map (lambda (a) (node->value session vars a))
                                     (vector-ref second 2))))
                   (else
                    (apply-name (cons #f ":")
                                (map (lambda (a) (node->value session vars a))
                                     args)))))
               (apply-name (cons #f name)
                           (map (lambda (a) (node->value session vars a))
                                args)))))
        (else #f))))

  ;;; ---------------------------------------------------------------------
  ;;; Function-reference resolution
  ;;;
  ;;; `fun name/arity` is surface syntax for a first-class reference to a
  ;;; declared function, so a string read at run time must produce the
  ;;; same `/`(flat-name, arity) closure a compiled occurrence of that
  ;;; spelling does. The reader has no renamer, so it resolves the name
  ;;; against the session's callables table — the same table
  ;;; `%apply-closure` dispatches through — and rewrites the parsed shape
  ;;; before `node->value` builds the term. The identity is read back off
  ;;; the matching callable key, never re-derived, so a resolved
  ;;; reference always dispatches.
  ;;;
  ;;; Without a renamer the module of an unqualified name is not known,
  ;;; so resolution is program-wide, exactly like the synthetic
  ;;; `<query>` module the reference's renamer builds for top-level
  ;;; goals: a bare name matches any module's function of that base and
  ;;; arity, two matches are an ambiguity, and a `module:name` spelling
  ;;; (accepted only by this reader) picks one exactly. The reader does
  ;;; not implement `quote/1`, so `fun` resolves inside `quote(...)`
  ;;; too.
  ;;; ---------------------------------------------------------------------

  ;; The parsed surface shape of `fun name/arity`: a one-argument `fun`
  ;; compound whose argument is a two-argument `/` compound with an
  ;; integer arity and a literal name. Anything else — `fun(X)`
  ;; parameters, `fun X/1`, a negative arity — is not a reference and
  ;; stays data.
  (define (funref-shape? node)
    (and (vector? node)
         (eq? (vector-ref node 0) 'compound)
         (string=? (vector-ref node 1) "fun")
         (= (length (vector-ref node 2)) 1)
         (let ((inner (car (vector-ref node 2))))
           (and (vector? inner)
                (eq? (vector-ref inner 0) 'compound)
                (string=? (vector-ref inner 1) "/")
                (= (length (vector-ref inner 2)) 2)
                (let ((name-node (car (vector-ref inner 2)))
                      (arity-node (cadr (vector-ref inner 2))))
                  (and (eq? (vector-ref arity-node 0) 'int)
                       (>= (vector-ref arity-node 1) 0)
                       (funref-name name-node)))))))

  ;; The surface name of a `fun` name node, as `(module . base)` — the
  ;; same split `Types.Name` carries, module `#f` when unqualified.
  ;; `#f` for anything that is not a literal atom.
  (define (funref-name node)
    (cond
      ((and (vector? node) (eq? (vector-ref node 0) 'atom))
       (cons #f (vector-ref node 1)))
      ((and (vector? node)
            (eq? (vector-ref node 0) 'compound)
            (string=? (vector-ref node 1) ":")
            (= (length (vector-ref node 2)) 2)
            (eq? (vector-ref (car (vector-ref node 2)) 0) 'atom)
            (eq? (vector-ref (cadr (vector-ref node 2)) 0) 'atom))
       (cons (vector-ref (car (vector-ref node 2)) 1)
             (vector-ref (cadr (vector-ref node 2)) 1)))
      (else #f)))

  ;; The first colon in `s`, or #f. The module part of an identity never
  ;; contains a colon, and the base may, so only the first one splits.
  (define (first-colon s)
    (let loop ((i 0))
      (cond ((>= i (string-length s)) #f)
            ((char=? (string-ref s i) #\:) i)
            (else (loop (+ i 1))))))

  (define (funref-base s)
    (let ((i (first-colon s)))
      (if i (substring s (+ i 1) (string-length s)) s)))

  ;; Does identity symbol `ident` name the function surface name `name`
  ;; denotes? An unqualified name matches any module's function of that
  ;; base; a qualified one matches the flattened identity exactly.
  (define (funref-matches? name ident)
    (let ((s (symbol->string ident)))
      (if (car name)
          (string=? s (flatten-name name))
          (string=? (funref-base s) (cdr name)))))

  ;; The surface spelling of a reference, for diagnostics.
  (define (funref-label name arity)
    (string-append (flatten-name name) "/" (number->string arity)))

  ;; Join strings with ", " (`string-join` is not R6RS).
  (define (comma-join strings)
    (cond ((null? strings) "")
          ((null? (cdr strings)) (car strings))
          (else (string-append (car strings) ", " (comma-join (cdr strings))))))

  ;; Order identities by their printed form. The callables table is a
  ;; hashtable, so its key order is not specified; sorting makes the
  ;; ambiguity list deterministic and matches the reference's ordered
  ;; map output.
  (define (sort-identities idents)
    (define (insert ident sorted)
      (cond ((null? sorted) (list ident))
            ((string<? (symbol->string ident) (symbol->string (car sorted)))
             (cons ident sorted))
            (else (cons (car sorted) (insert ident (cdr sorted))))))
    (let loop ((rest idents) (acc '()))
      (if (null? rest)
          acc
          (loop (cdr rest) (insert (car rest) acc)))))

  ;; Resolve `fun name/arity` against the session's callables: the
  ;; flattened identity on a unique match, a failure message when no
  ;; function matches or several do. Returns (values ok text), where a
  ;; `#f` flag marks `text` as an error message.
  (define (resolve-funref-name session name arity)
    (let loop ((keys (vector->list (hashtable-keys (session-callables session))))
               (matches '()))
      (if (null? keys)
          (cond
            ((null? matches)
             (values
              #f
              (string-append
               "read_term_from_string: unknown function '"
               (funref-label name arity)
               "'")))
            ((null? (cdr matches))
             (values #t (symbol->string (car matches))))
            (else
             (values
              #f
              (string-append
               "read_term_from_string: ambiguous function reference '"
               (funref-label name arity)
               "' (could be: "
               (comma-join
                (map (lambda (ident)
                       (string-append (symbol->string ident) "/"
                                      (number->string arity)))
                     (sort-identities matches)))
               ")"))))
          (let* ((key (car keys))
                 (functor (car key))
                 (identity (cadr key))
                 (key-arity (caddr key)))
            (loop (cdr keys)
                  (if (and (eq? functor '/)
                           (= key-arity arity)
                           (funref-matches? name identity))
                      (cons identity matches)
                      matches))))))

  ;; The `(module . base)` split of a flat name atom: `foo` is
  ;; unqualified, `module:foo` is qualified at the first colon. Used for
  ;; a dynamically built `fun name/arity` term, and for the flat
  ;; `module:name` identities the callables table is keyed on.
  (define (flat-name->name ident)
    (let* ((s (symbol->string ident))
           (i (first-colon s)))
      (if i
          (cons (substring s 0 i) (substring s (+ i 1) (string-length s)))
          (cons #f s))))

  ;; Resolve a flat surface name atom (`foo` or `module:foo`) and arity to
  ;; the callables identity, or #f. Exported for the runtime's dynamic
  ;; `fun` dispatch: a term built at run time carries a flat atom rather
  ;; than a parsed name node, but resolves through the same table and
  ;; matching rules.
  (define (resolve-funref-identity session ident arity)
    (let-values (((ok text) (resolve-funref-name session (flat-name->name ident) arity)))
      (if ok text #f)))

  ;; Rewrite every well-formed `fun name/arity` in the parsed node tree
  ;; to the canonical `/`(flat-name, arity) shape, recursing into
  ;; compound arguments. Returns (values #t node) on success and
  ;; (values #f message) when a name does not resolve.
  (define (resolve-funrefs session node)
    (cond
      ((funref-shape? node)
       (let* ((inner (car (vector-ref node 2)))
              (name-node (car (vector-ref inner 2)))
              (arity-node (cadr (vector-ref inner 2)))
              (name (funref-name name-node))
              (arity (vector-ref arity-node 1)))
         (let-values (((ok flat) (resolve-funref-name session name arity)))
           (if ok
               (values
                #t
                (vector 'compound "/"
                        (list (vector 'atom flat) arity-node)))
               (values #f flat)))))
      ((and (vector? node) (eq? (vector-ref node 0) 'compound))
       (let loop ((rest (vector-ref node 2)) (acc '()))
         (if (null? rest)
             (values #t (vector 'compound (vector-ref node 1) (reverse acc)))
             (let-values (((ok arg) (resolve-funrefs session (car rest))))
               (if ok
                   (loop (cdr rest) (cons arg acc))
                   (values #f arg))))))
      (else (values #t node))))

  ;;; Read a single term from `text` in `session`.
  ;;;
  ;;; The operator table is the session's (`session-op-table`), so a
  ;;; string can spell every operator the program can, exactly as the
  ;;; goal parser can. Returns two values: `(values #t value)` on
  ;;; success, and `(values #f message)` when the text is not a term (an
  ;;; empty input, a syntax error, or trailing input after a complete
  ;;; term). The caller decides how to report the failure.
  (define (parse-term session text)
    (let* ((ops (session-op-table session))
           (n (string-length text))
           (i (skip-sc text 0)))
      (if (>= i n)
          (values #f "read_term_from_string: unexpected end of input")
          (let ((t (parse-term-at ops text i max-prec)))
            (cond
              ((not t) (values #f "read_term_from_string: parse error"))
              ((< (cdr t) n)
               (values #f "read_term_from_string: unexpected input after term"))
              (else
               (let-values (((ok node) (resolve-funrefs session (car t))))
                 (if ok
                     (values #t (node->value session
                                             (make-hashtable string-hash string=?)
                                             node))
                     (values #f node)))))))))
)
