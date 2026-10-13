;;;; Unified runtime for generated CHR programs.
(library (ychr runtime)
  (export
    ;; Session
    make-session session? make-counters
    ;; From (ychr var)
    make-var var? var-id deref unify unifiable? equal?/chr
    make-term term? term-functor term-args
    match-term get-arg add-observer! ground-key get-var-id
    ;; From (ychr store)
    make-store-by-type create-constraint store-constraint
    kill-constraint alive-constraint?
    constraint-id constraint-arg constraint-type
    id-equal? is-constraint-type?
    store-snapshot snapshot-length snapshot-ref
    suspension? suspension-alive? suspension-arg
    suspension-id suspension-type
    ;; Store index (used by generated `Foreach` code)
    indexed-positions-for candidate-suspensions
    index-threshold
    ;; From (ychr history)
    add-history! not-in-history?
    ;; From (ychr reactivation)
    enqueue! drain-queue!
    ;; Helpers for generated code
    %unify %unifiable? %nonvar? %unbound? %chr-error %chr-inst-error
    chr-inst? %bool-from-value
    %print %write %writeln %panic %ground?
    %term-variables %compound-to-list %list-to-compound
    %name-base
    %read-term-from-string %write-term-to-string %write-store-to-list
    %print-store %run-chr-session %run-chr-session-ep
    %solve %fail %findall %fold-solutions
    %int-to-float %float-to-int
    %add %sub %mul %fdiv
    %lt %gt %le %ge
    %idiv %imod %irem
    %str-concat %str-length %str-upper %str-lower
    %copy-term
    %nil %cons
    ;; Deep-eval dispatch table for the @is@ operator
    register-evaluable! deep-eval-value
    ;; Closure-apply dispatch table for @'$call'@
    register-callable! %apply-closure
    ;; Dynamic tell dispatch table for @tell/N@
    register-tellable! %tell-term
    ;; Session initialization
    %make-session make-op-table
    ;; Search driver and its program-level tables
    %fork-session register-goal! register-short-export!
    search-failure?)
  (import (rnrs)
          (ychr session)
          (ychr var)
          (ychr store)
          (ychr history)
          (ychr reactivation)
          (ychr trail)
          (ychr optable)
          (ychr pretty)
          (ychr read))

  ;;; Session initialization: creates a fully initialized session.
  ;;;
  ;;; `ops` is the operator table `read_term_from_string` parses with:
  ;;; the program's own table, built by the generated library with
  ;;; `make-op-table` (see `Scheme.hs`'s `opTableSExpr`). The shorter
  ;;; clauses install `builtin-op-table`, the counterpart of the
  ;;; `builtinOps` `initSessionEnv` gives a hand-built interpreter
  ;;; session. They install no constraint type names either, so a
  ;;; hand-built session's stored constraints label as `c#type_N` in
  ;;; `write_store_to_list` and `print_store`.
  ;;;
  ;;; A session built here owns its store: its `owner` token is the
  ;;; `store-by-type` object itself, which is what makes the reactivation
  ;;; queue's foreign-suspension filter answer correctly for a fresh
  ;;; `run_chr_session` fork (`%fork-session`).
  (define %make-session
    (case-lambda
      ;; A session with no store index. Hand-built sessions (the unit
      ;; tests) and any caller that does not know the program's index
      ;; positions take this clause; the store then scans, exactly as it
      ;; did before the index existed.
      ((num-types)
       (%make-session num-types '() builtin-op-table (vector)))
      ;; `positions` is the compiler-emitted alist of the (constraint
      ;; type, argument position) pairs the program looks a partner up
      ;; through an index condition: one `(cons TYPE (list POS ...))` per
      ;; type, built by `Scheme.hs`'s `indexPositionsSExpr` from
      ;; `YCHR.Internal.VM.Index.indexablePositions`. Only those
      ;; positions are recorded in the store index, and only those may be
      ;; looked up in it; anything else falls back to the scan.
      ((num-types positions)
       (%make-session num-types positions builtin-op-table (vector)))
      ((num-types positions ops)
       (%make-session num-types positions ops (vector)))
      ;; `type-names` is the compiler-emitted source name of every
      ;; constraint type, one per type index, in the mangled `vmName`
      ;; form (built by `Scheme.hs`'s `typeNamesSExpr` from
      ;; `CompiledProgram.typeNames`). `write_store_to_list` and
      ;; `print_store` split it back into a module and a base name.
      ((num-types positions ops type-names)
       (%make-session num-types
                      positions
                      ops
                      type-names
                      (make-vector num-types #f)))
      ;; `inert` is the compiler-emitted inert-type vector: one boolean
      ;; per constraint type, `#t` for a type whose activation runs no
      ;; occurrence procedure (built by `Scheme.hs`'s `inertTypesSExpr`
      ;; from `CompiledProgram.inertTypes`). `store-constraint` skips
      ;; observer registration for those types — the Delay Avoidance
      ;; optimization's trivial instance. The clause above defaults it to
      ;; "none inert", which is what a hand-built session or an older
      ;; generated library gets.
      ((num-types positions ops type-names inert)
       (let ((store (make-store-by-type num-types))
             (counter (make-counters 0 0))
             ;; A session is only ever asked about a type index below its
             ;; own type count, so this table is sized by that count. A
             ;; hand-built session passes a shorter (often empty)
             ;; type-name vector, so its length is not a safe bound.
             (inert* (if (>= (vector-length inert) num-types)
                         inert
                         (let ((v (make-vector num-types #f)))
                           (do ((i 0 (+ i 1))) ((= i (vector-length inert)))
                             (vector-set! v i (vector-ref inert i)))
                           v))))
         (make-session
          counter
          store
          (make-index-positions num-types positions)
          (make-store-index num-types)
          type-names
          (make-hashtable equal-hash equal?)
          '()
          '()
          ;; Deep-eval dispatch table: keys are
          ;; (functor-symbol . arity) pairs; values are the
          ;; procedures the deep-evaluator calls when @is@
          ;; walks a @VTerm@ matching the key. Generated
          ;; libraries fill this in via @register-evaluable!@.
          (make-hashtable evaluable-key-hash evaluable-key-eq?)
          ;; Closure-apply dispatch table: keys are
          ;; (functor identity arity) lists; values are the
          ;; procedures `%apply-closure` calls for that
          ;; closure. Generated libraries fill this in via
          ;; @register-callable!@.
          (make-hashtable equal-hash equal?)
          ;; Dynamic tell dispatch table: keys are
          ;; ("scope" functor arity) lists; values are the tell
          ;; procedures `%tell-term` calls. Generated libraries
          ;; fill this in via @register-tellable!@.
          (make-hashtable equal-hash equal?)
          ops
          ;; The search tables. `goals`, `exported-goals` and
          ;; `short-exports` are filled by the generated library's
          ;; `register-goal!` and `register-short-export!`; `alt-type` is
          ;; derived here from `type-names`, so no emission is needed for
          ;; it. `exported-goals` is the subset of `goals` the program
          ;; exports: a caller-written qualified goal is checked against
          ;; it, while a lifted disjunct — registered but not exported —
          ;; stays reachable from a choice point's alternatives.
          (make-hashtable equal-hash equal?)
          (make-hashtable equal-hash equal?)
          (make-hashtable equal-hash equal?)
          inert*
          (alt-type-of type-names)
          store)))))
  ;;; The constraint type holding `search:alt/1`, or `#f` when the
  ;;; program never declares it. Derived from the mangled type-name
  ;;; table: `search:alt` is a qualified name, so its `vmName` is
  ;;; `search__alt`. A program with no `alt` type answers `#f` and the
  ;;; driver simply finds no choice points — the honest reading of a goal
  ;;; with no alternatives in it.
  (define (alt-type-of names)
    (let ((target "search__alt")
          (n (vector-length names)))
      (let loop ((i 0))
        (cond ((>= i n) #f)
              ;; The table holds the mangled name as a *string* — the
              ;; compiler emits a `(vector "…")` literal — so the compare
              ;; is `string=?`, not `eq?`.
              ((and (string? (vector-ref names i))
                    (string=? (vector-ref names i) target))
               i)
              (else (loop (+ i 1)))))))

  ;;; A session of the same program, ready to run a search. Both modes
  ;;; share the program-level tables, the counters, the value tables and
  ;;; the trail (a global box, see `(ychr trail)`), and give the fork an
  ;;; empty reactivation queue.
  ;;;
  ;;;   * `'copy` — `solve`, `findall` and `fold_solutions` — *shares* the
  ;;;     caller's `store-by-type`, `store-index` and `history` objects.
  ;;;     No copy is made: every write to them is trailed at the mutation
  ;;;     choke points and every driver exit unwinds to the base mark, so
  ;;;     the caller gets them back as they were. This is the Scheme
  ;;;     counterpart of the Haskell runtime's four pointer reads.
  ;;;   * `'fresh` — `run_chr_session` and `_ep` — starts from an empty
  ;;;     store, an empty store index and an empty history, and its own
  ;;;     owner token, so a constraint of the caller's is neither visible
  ;;;     to the goal nor reactivated by it.

  (define (%fork-session s mode)
    (let* ((num-types (vector-length (session-store-by-type s)))
           (copy? (eq? mode 'copy))
           (store (if copy?
                      (session-store-by-type s)
                      (make-store-by-type num-types))))
      (make-session
       (session-counters s)
       store
       (session-index-positions s)
       (if copy? (session-store-index s) (make-store-index num-types))
       (session-type-names s)
       (if copy? (session-history s) (make-hashtable equal-hash equal?))
       '()
       '()
       (session-evaluables s)
       (session-callables s)
       (session-tellables s)
       (session-op-table s)
       (session-goals s)
       (session-short-exports s)
       (session-exported-goals s)
       (session-inert s)
       (session-alt-type s)
       (if copy? (session-owner s) store))))

  ;;; Register the tell procedure of one declared constraint, keyed by the
  ;;; functor a compiled term of that constraint carries and its arity.
  ;;; The generated library calls this for every constraint it declares
  ;;; that has a tell procedure — exported or not, because a choice
  ;;; point's alternatives routinely name module-internal constraints the
  ;;; compiler itself lifted out of a `;`.
  ;;;
  ;;; `exported?` is recorded so a goal error can say whether a name is
  ;;; unknown or merely not exported; the driver decides the latter from
  ;;; `short-exports` before it ever looks here.

  (define (register-goal! s functor arity tell-proc exported?)
    (hashtable-set! (session-goals s)
                    (cons functor arity)
                    (cons tell-proc (if exported? #t #f)))
    ;; The export flag is what lets a *caller-written* qualified goal be
    ;; rejected with "Constraint not exported", mirroring the Haskell
    ;; driver's `Set.member`. It is deliberately separate from the goal
    ;; table: a lifted disjunct is registered but never exported, and the
    ;; alternatives of a choice point must still reach it.
    (when exported?
      (hashtable-set! (session-exported-goals s) (cons functor arity) #t)))

  ;;; Register one *unqualified* surface name with the module that
  ;;; exports it, so a caller-supplied goal spelled without a qualifier
  ;;; resolves the way the source program's own would: the module
  ;;; qualification the compiler would have applied. `target` is the
  ;;; resolved mangled functor, or a list of module names when several
  ;;; modules export the same name and arity, which the driver reports as
  ;;; ambiguous.

  (define (register-short-export! s name arity target)
    (hashtable-set! (session-short-exports s) (cons name arity) target))

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
  ;; recursion continues on the dereferenced value. Dispatch is
  ;; `evaluable-key-proc`, which tries the session's evaluables table
  ;; and then the prelude host-call table (see its comment for the
  ;; three tiers).
  ;;
  ;; A term built from a `host:` call in data position keeps `host__F`
  ;; as its functor, exactly as a declared function keeps its
  ;; qualified vmName. The evaluables table holds neither, so the
  ;; functor is decoded (`host__F` -> `host:F` -> `F`) and retried
  ;; against the host table. That is what makes
  ;; `T = host:'+'(1, 1), R is T.` evaluate to 2 rather than
  ;; reporting `host__+/2`.
  ;;
  ;; `X = '+'(1, 1), R is X.` does *not* go through that decode: the
  ;; compiler canonicalizes the surface `+` to the qualified
  ;; `prelude__+`, which the evaluables table answers directly. The
  ;; host table's bare `+` entry is reached only by a functor that
  ;; never went through canonicalization — a `quote`d atom, say.
  ;;
  ;; A non-evaluable functor raises a runtime error that names it in
  ;; decoded surface form (`host:-/1`, `pair/2`), matching the Haskell
  ;; interpreter's message.
  ;;
  ;; Arguments are walked by `deep-argument`. The rule there follows
  ;; the split the direct path already makes: the arguments of a
  ;; /declared/ call are expressions that get evaluated, while a
  ;; constructor is data and keeps its shape — though a variable inside
  ;; it is still dereferenced, so the data carries the most recent
  ;; bindings. That is what makes `T = member(1, [0, 1, 2]), R is T`
  ;; (with `library(lists)` imported) work: the list argument stays
  ;; data instead of being dispatched as a call, exactly as it behaves
  ;; when the call is written inline (`R is member(1, [0, 1, 2])`).
  ;; Walking the arguments with `deep-eval-value` used to dispatch the
  ;; cons cell and report `is: functor is not evaluable: prelude:./2`.
  ;; The /outermost/ compound is still required to be evaluable: the
  ;; not-evaluable error is raised for it, so `T = pair(1, 2), R is T`
  ;; keeps failing as before.
  (define (deep-eval-value s v)
    (let ((d (deref v)))
      (cond
        ((term? d)
         (let* ((functor (term-functor d))
                (args (term-args d))
                (n (vector-length args))
                (proc (evaluable-key-proc s functor n)))
           (if proc
               (let ((eval-args (make-vector n)))
                 (do ((i 0 (+ i 1))) ((= i n))
                   (vector-set! eval-args i
                                (deep-argument s (vector-ref args i))))
                 (apply proc s (vector->list eval-args)))
               ;; Match the Haskell interpreter's message format:
               ;; "is: functor is not evaluable: <functor>/<arity>"
               ;; (single concatenated string, no separate detail).
               (%chr-error
                (string-append "is: functor is not evaluable: "
                               (decode-mangled-name
                                (symbol->string functor))
                               "/"
                               (number->string n))))))
        (else d))))

  ;; Walk one argument of a deep-evaluated call: dereference it, then
  ;; evaluate it if its functor names a call. A compound that is not a
  ;; call is data: it is kept as-is, with its own subterms walked by
  ;; `deep-data` so that bound variables inside it are still resolved.
  (define (deep-argument s v)
    (let ((d (deref v)))
      (cond
        ((term? d)
         (let* ((functor (term-functor d))
                (args (term-args d))
                (n (vector-length args))
                (proc (evaluable-key-proc s functor n)))
           (if proc
               (let ((eval-args (make-vector n)))
                 (do ((i 0 (+ i 1))) ((= i n))
                   (vector-set! eval-args i
                                (deep-argument s (vector-ref args i))))
                 (apply proc s (vector->list eval-args)))
               (deep-data s d))))
        (else d))))

  ;; Walk a data compound — one whose functor is not a call. Its shape
  ;; is preserved and its subterms are never dispatched, but variables
  ;; reachable through it are dereferenced so the data reflects current
  ;; bindings.
  (define (deep-data s v)
    (let ((d (deref v)))
      (cond
        ((term? d)
         (let* ((args (term-args d))
                (n (vector-length args))
                (out (make-vector n)))
           (do ((i 0 (+ i 1))) ((= i n))
             (vector-set! out i (deep-data s (vector-ref args i))))
           (make-term (term-functor d) out)))
        (else d))))

  ;; The procedure the deep evaluator calls for a (functor, arity)
  ;; pair, or #f when the pair is not evaluable. Three tiers, in the
  ;; same order the Haskell interpreter's `invokeByKey` uses:
  ;;
  ;;   1. the session's evaluables table — user-defined functions and
  ;;      the prelude's CHR functions, keyed by the fully-qualified VM
  ;;      functor (`prelude__+`);
  ;;   2. the prelude host-call table under the raw functor — a bare
  ;;      host name (`copy_term`) as built by `quote`, or by a source
  ;;      atom that was never canonicalized;
  ;;   3. the prelude host-call table under the bare name of a `host:`
  ;;      functor (`host__F`), since its (name, arity) key is not the
  ;;      raw one.
  ;;
  ;; The decoded `host:F` form is matched structurally as the vmName
  ;; `host__F`, never as a decoded string: an unqualified atom may
  ;; itself read `host:…` (a source atom `'host:write'` encodes to
  ;; `host:write` — ASCII passes through the encoder — and only
  ;; /decodes/ to the same text a `host__write` functor does), and only
  ;; the mangled shape — module `host`, separator, base free of any
  ;; further separator — is a host call.
  (define (evaluable-key-proc s functor n)
    (let ((key (make-evaluable-key functor n))
          (raw (symbol->string functor)))
      (or (hashtable-ref (session-evaluables s) key #f)
          (hashtable-ref *prelude-host-calls* key #f)
          (let ((bare (host-bare-name raw)))
            (and bare
                 (hashtable-ref *prelude-host-calls*
                                (make-evaluable-key bare n)
                                #f))))))

  ;; The bare name of a `host:` functor, or #f when the functor is not
  ;; one. The argument is the /raw/ mangled functor text, because the
  ;; mangling is what carries the module split: `host__F` is a host
  ;; call. An unqualified source atom spelled `'host:F'` stays
  ;; unqualified (`host:F`, no separator) and is therefore not one;
  ;; every unqualified name has no separator of its own, since the
  ;; lexer rejects `__` inside a source atom.
  (define (host-bare-name raw)
    (let ((sep (find-double-underscore raw)))
      (and sep
           (> sep 0)
           (not (find-double-underscore (substring raw (+ sep 2)
                                                  (string-length raw))))
           (string=? (decode-mangled-name (substring raw 0 sep)) "host")
           (string->symbol
            (decode-mangled-name (substring raw (+ sep 2)
                                            (string-length raw)))))))

  ;; Find the first occurrence of "__" in `s`, or #f.
  (define (find-double-underscore s)
    (let ((n (string-length s)))
      (let loop ((i 0))
        (cond
          ((> (+ i 2) n) #f)
          ((and (char=? (string-ref s i) #\_)
                (char=? (string-ref s (+ i 1)) #\_))
           i)
          (else (loop (+ i 1)))))))

  ;;; --- Closure-apply dispatch for `'$call'` ---

  ;; A key identifies a callable by the shape of the closure value that
  ;; designates it: the closure term's functor, its identity field (a
  ;; flattened function name for a function reference, a lambda
  ;; identifier for a lifted lambda) and the arity the callable was
  ;; declared at. Keys are `(functor identity arity)` lists, hashed with
  ;; `equal-hash`/`equal?` — symbols compare by name under both, so a
  ;; key built here matches one built by `register-callable!`. Mirrors
  ;; the Haskell runtime's `CallableKey` table
  ;; (`YCHR.Internal.Runtime.Monad.CallableRegistry`).
  (define (make-callable-key functor identity arity)
    (list functor identity arity))

  ;; Register a procedure to invoke when `%apply-closure` is handed a
  ;; closure whose key matches. The procedure must accept
  ;; (session arg1 ... argN) — the same calling convention used by
  ;; generated user-function procedures — and is called with the
  ;; closure's captured values before the application arguments.
  (define (register-callable! s functor identity arity proc)
    (hashtable-set! (session-callables s)
                    (make-callable-key functor identity arity)
                    proc))

  ;; Apply a first-class callable to arguments: the whole of
  ;; `'$call'(F, A1, ..., An)`. Mirrors `applyClosure` in the Haskell
  ;; interpreter, including which failure raises which kind of error.
  ;;
  ;; A closure value is a compound term whose functor says which kind of
  ;; callable it is and whose first field identifies it:
  ;;
  ;;   * `/`(Identity, Arity) — a function reference. The identity is
  ;;     the flattened source name (`module:name`); the declared arity
  ;;     is the second field, and an application at any other arity is
  ;;     a definite mismatch (not a redirect to a same-named function
  ;;     of that arity).
  ;;   * `__closure`(Identity, SourceForm, Capture ...) — a lifted
  ;;     lambda. The arity is the one it is applied at, because the
  ;;     closure does not record the arity its source lambda declared;
  ;;     the table only holds that declared arity, so any other arity
  ;;     misses. Captures are the fields after the quoted source form.
  ;;
  ;; A value `callable-invocation` does not recognize may still be the
  ;; surface shape of a function reference, `fun('/`(name, arity))` —
  ;; what `list_to_compound` and friends build at run time, with no
  ;; renamer to resolve the name. `dynamic-funref-key` resolves that name
  ;; against the same callables table, so a dynamically constructed
  ;; reference is callable exactly like one the string reader produced.
  (define (%apply-closure s closure . args)
    (let* ((d (deref closure))
           (n (length args))
           (hit (and (term? d) (callable-invocation d n))))
      (cond
        (hit
         (let* ((key (car hit))
                (captures (cdr hit))
                (proc (hashtable-ref (session-callables s) key #f)))
           (if proc
               (apply proc s (append captures args))
               (%chr-error "call: no matching closure"))))
        ((dynamic-funref-key s d n)
         =>
         (lambda (key)
           (let ((proc (hashtable-ref (session-callables s) key #f)))
             (if proc
                 (apply proc s args)
                 (%chr-error "call: no matching closure")))))
        ((%unbound? d)
         (%chr-inst-error
          (string-append
           "'$call': closure argument is not sufficiently instantiated"
           " (unbound variable)")))
        (else (%chr-error "call: no matching closure")))))

  ;;; --- Dynamic tell dispatch for `tell/N` ---

  ;; The list constructor or the empty list, in both spellings. Mirrors
  ;; `isListFunctor` in `YCHR.Internal.Runtime.Registry`.
  (define list-functors
    (map string->symbol '("prelude__." "." "prelude__[]" "[]")))
  (define (list-functor? f) (and (memq f list-functors) #t))

  ;; Register the tell procedure a `tell/N` written in module `scope`
  ;; reaches for a goal with this functor at this total arity. Keys are
  ;; `(scope functor arity)` lists — a string, a symbol and an integer —
  ;; hashed with `equal-hash`/`equal?`. Mirrors the Haskell runtime's
  ;; `TellableKey` table (`YCHR.Internal.Runtime.Monad.TellableRegistry`).
  (define (register-tellable! s scope functor arity proc)
    (hashtable-set! (session-tellables s) (list scope functor arity) proc))

  ;; Tell a constraint chosen at run time: the whole of a dynamic
  ;; `tell(G, A1, ..., Ak)` written in module `scope`. Mirrors `tellTerm`
  ;; in the Haskell interpreter, including which failure raises which
  ;; kind of error. An atom goal contributes no arguments of its own and
  ;; a compound its own, ahead of the appended ones; they are passed on
  ;; un-dereferenced, as a direct tell's would be. A list can only be a
  ;; malformed goal, and is reported as not a constraint term.
  (define (%tell-term s scope goal . extras)
    (let ((d (deref goal)))
      (define (dispatch functor args)
        (let* ((all (append args extras))
               (n (length all))
               (proc (hashtable-ref (session-tellables s)
                                    (list scope functor n)
                                    #f)))
          (if proc
              (apply proc s all)
              (%chr-error
               (string-append
                "tell: no constraint "
                (decode-mangled-name (symbol->string functor))
                "/"
                (number->string n)
                " is visible in module "
                scope)))))
      (cond
        ((and (symbol? d) (not (list-functor? d))) (dispatch d '()))
        ((and (term? d) (not (list-functor? (term-functor d))))
         (dispatch (term-functor d) (vector->list (term-args d))))
        ((%unbound? d)
         (%chr-inst-error
          "tell: goal is not sufficiently instantiated (unbound variable)"))
        (else (%chr-error "tell: goal is not a constraint term")))))

  ;; The dispatch key of a closure value applied at `n` arguments,
  ;; paired with the captured values to pass before those arguments —
  ;; or #f when the value is not a closure applied at a valid arity.
  ;;
  ;; The two header fields are read through `deref`, the way the
  ;; generated dispatchers' `equal?/chr` comparisons were: a function
  ;; reference whose name or declared-arity field is a bound variable
  ;; still dispatches. Captures (everything after the header) are left
  ;; alone, exactly as `get-arg` handed them to the callee.
  (define (callable-invocation d n)
    (let ((functor (term-functor d))
          (fields (term-args d)))
      (cond
        ((and (eq? functor '/)
              (= (vector-length fields) 2))
         (let ((ident (deref (vector-ref fields 0)))
               (arity (deref (vector-ref fields 1))))
           ;; `exact-integer?` is R7RS; this runtime is R6RS.
           (if (and (symbol? ident)
                    (integer? arity)
                    (exact? arity)
                    (= arity n))
               (cons (make-callable-key functor ident n) '())
               #f)))
        ((and (eq? functor '__closure)
              (>= (vector-length fields) 2))
         (let ((ident (deref (vector-ref fields 0))))
           (if (symbol? ident)
               (cons (make-callable-key functor ident n)
                     (list-tail (vector->list fields) 2))
               #f)))
        (else #f))))

  ;; The dispatch key of a surface-shaped `fun name/arity` term applied at
  ;; `n` arguments, or #f for any other value.
  ;;
  ;; Such a term has functor `fun` and a single `/` argument holding the
  ;; name and declared arity, exactly the shape the renamer strips from
  ;; source. Built at run time it carries no resolved identity, so the
  ;; name atom is resolved against the callables table here, with the
  ;; same matching rules as the string reader
  ;; (`resolve-funref-identity`). Both failures — no match, several
  ;; matches — leave the term uncallable, and `%apply-closure` reports
  ;; the ordinary `call: no matching closure`.
  ;;
  ;; Runs only after `callable-invocation` misses, and only inspects
  ;; values whose functor is `fun`, so the common dispatch path is
  ;; untouched.
  (define (dynamic-funref-key s d n)
    (and (term? d)
         (eq? (term-functor d) 'fun)
         (let ((fields (term-args d)))
           (and (= (vector-length fields) 1)
                (let ((inner (deref (vector-ref fields 0))))
                  (and (term? inner)
                       (eq? (term-functor inner) '/)
                       (let ((inner-fields (term-args inner)))
                         (and (= (vector-length inner-fields) 2)
                              (let ((ident (deref (vector-ref inner-fields 0)))
                                    (declared (deref (vector-ref inner-fields 1))))
                                (and (symbol? ident)
                                     (integer? declared)
                                     (exact? declared)
                                     (= declared n)
                                     (let ((flat
                                            (resolve-funref-identity
                                             s ident declared)))
                                       (and flat
                                            (make-callable-key
                                             '/ (string->symbol flat) n)))))))))))))

  ;; Prelude host-call table for `deep-eval-value`. Mirrors the
  ;; bare-name entries in Haskell's `baseHostCallRegistry`
  ;; (`src/YCHR/Internal/Runtime/Registry.hs`), plus `print`,
  ;; `read_term_from_string` and `write_term_to_string`, the reachable
  ;; entries of `metaHostCallRegistry` (`src/YCHR/Internal/Meta.hs`).
  ;; `name_base` and the unimplemented meta calls are deliberately left
  ;; out (see dev-docs/SCHEME_BACKEND_GAPS.md), and so are
  ;; `print_store` and `write_store_to_list`: their only arity is 0, and
  ;; a nullary `host:` spelling compiles to an atom, so the deep
  ;; evaluator — which dispatches only `term?` values — can never ask
  ;; for their key. It is consulted both
  ;; under the raw functor and under the bare name decoded out of a
  ;; `host:` functor (`evaluable-key-proc`); the raw route is what
  ;; answers a bare atom that no canonicalization qualified, such as
  ;; one built by `quote`. Each procedure receives the session as its
  ;; first argument (uniform with user-defined functions); host calls
  ;; that don't need it ignore the parameter. Keep this list in sync
  ;; with the registries above when adding new bare-name host calls.
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
      ;; Output. `%write`/`%writeln` classify a bound non-string the
      ;; same way `writeStr`/`writeStrLn` do in
      ;; `src/YCHR/Internal/Runtime/Registry.hs`, so a `host:` term in
      ;; data position (`T = host:writeln("x"), R is T.`) behaves
      ;; identically on both backends.
      (h 'write 1 (lambda (s v) (%write v)))
      (h 'writeln 1 (lambda (s v) (%writeln v)))
      (h 'panic 1 (lambda (s v) (%panic v)))
      ;; Meta. `print` is the meta registry's pretty-printer (`%print`
      ;; above), which returns the unit atom. Registered at arity 1 —
      ;; the only arity `library(meta)` declares; the direct
      ;; `host:print(...)` path handled by `hostCallMap` is variadic.
      (h 'print 1 (lambda (s v) (%print v)))
      ;; `read_term_from_string` is the meta registry's reader, which
      ;; needs the session to allocate the fresh variables of `_` and of
      ;; the named variables it shares.
      (h 'read_term_from_string 1 (lambda (s v) (%read-term-from-string s v)))
      ;; `write_term_to_string` is the meta registry's writer. Unlike
      ;; its reader counterpart it needs no session — it only renders,
      ;; and an unbound variable renders as `_` rather than allocating
      ;; anything.
      (h 'write_term_to_string 1 (lambda (s v) (%write-term-to-string v)))
      (h 'term_variables 1 (lambda (s v) (%term-variables v)))
      (h 'compound_to_list 1 (lambda (s v) (%compound-to-list v)))
      (h 'list_to_compound 1 (lambda (s v) (%list-to-compound v)))
      (h 'copy_term 1 (lambda (s v) (%copy-term s v)))
      ;; library(search): each reads the store or a session table, so all
      ;; take the session first; `fail` reads only the trail but keeps
      ;; the same convention.
      (h 'solve 1 (lambda (s goal) (%solve s goal)))
      (h 'findall 2 (lambda (s template goal) (%findall s template goal)))
      (h 'fold_solutions 4 (lambda (s template goal f acc)
                             (%fold-solutions s template goal f acc)))
      (h 'fail 0 (lambda (s) (%fail s)))
      (h 'run_chr_session 1 (lambda (s goal) (%run-chr-session s goal)))
      (h 'run_chr_session_ep 1 (lambda (s goal)
                                 (%run-chr-session-ep s goal)))
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

  ;;; Print. Mirrors `print` in `YCHR.Internal.Meta`: every argument is
  ;;; rendered with the surface pretty-printer (`prettyTerm` on the
  ;;; Haskell side) on its own line, and the unit atom is returned.
  ;;; Variadic because the Haskell registry is keyed by name alone, so a
  ;;; `host:print(a, b)` call prints both.
  (define (%print . args)
    (for-each (lambda (v) (display (pretty-term v)) (newline)) args)
    (%unit))

  ;;; Write / writeln. `display` accepts any value, so on its own it
  ;;; has no failure path to classify; `writeStr`/`writeStrLn` in the
  ;;; Haskell registry match `[VText s]` and so reject a bound
  ;;; non-string as well as diagnosing an unbound one. Demanding a
  ;;; string here is what makes the two agree — and what keeps the
  ;;; general message reachable rather than dead. `prelude.chr`
  ;;; declares `write(string)`, so only untyped and `host:` call paths
  ;;; could reach the rejection at all.
  ;;
  ;;; Both return the unit atom `()`, as `unit` in
  ;;; `src/YCHR/Internal/Runtime/Registry.hs` does. The `write`/`writeln`
  ;;; prelude wrappers are declared `-> any`, so the value is otherwise
  ;;; discarded; returning it keeps a `host:` term used as data
  ;;; (`T = host:writeln("x"), R is T.`) from yielding the host
  ;;; language's unspecified value on one backend only.
  (define (%write v)
    (if (string? v)
        (begin (display v) (%unit))
        (%arg-error "write" (list v) "write: expected 1 Text argument")))
  (define (%writeln v)
    (if (string? v)
        (begin (display v) (newline) (%unit))
        (%arg-error "writeln" (list v) "writeln: expected 1 Text argument")))

  ;;; The prelude's `panic/1`, mirroring `panicHost` in
  ;;; `src/YCHR/Internal/Runtime/Registry.hs`: the message is the
  ;;; user's, verbatim.
  (define (%panic v)
    (if (string? v)
        (%chr-error v)
        (%arg-error "panic" (list v) "panic: expected 1 Text argument")))

  ;;; The unit value: the atom `()`, Haskell's `VAtom "()"`.
  (define (%unit) (string->symbol "()"))

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

  ;;; read_term_from_string: read one term out of a string, mirroring
  ;;; `read_term_from_string` in `YCHR.Internal.Meta` (`parseTermWith`
  ;;; over the session's operator table, followed by `termToValue`). The
  ;;; parser itself lives in `(ychr read)` so it can be documented on
  ;;; its own; this is the host-call entry point. The session is
  ;;; threaded for the fresh variables of `_` and of named variables and
  ;;; for its operator table (`session-op-table`), so the string can
  ;;; spell every operator the program can.
  ;;;
  ;;; A non-string argument is classified like the other strict
  ;;; primitives: an unbound variable is an instantiation failure (so a
  ;;; rule guard delays and is retried), a bound non-string a general
  ;;; one. A parse failure is always a general CHR error — there is no
  ;;; value the caller could have meant.
  (define (%read-term-from-string session text)
    (if (string? text)
        (let-values (((ok result) (parse-term session text)))
          (if ok result (%chr-error result)))
        (%arg-error "read_term_from_string" (list text)
                    "read_term_from_string: expected 1 Text argument")))

  ;;; write_term_to_string: render one value in surface syntax, the
  ;;; inverse of the reader above and a port of
  ;;; `write_term_to_string` in `YCHR.Internal.Meta` (`prettyValue`,
  ;;; i.e. `prettyTerm` over an empty alias map). `pretty-term` is the
  ;;; shared printer, so the spelling — atom quoting, `(…)` around
  ;;; negative numbers, list syntax, `true`/`false` — agrees with
  ;;; `%print`, `%unify`'s failure messages and the drivers. Flonums
  ;;; are the one exception, and a pre-existing one: each host formats
  ;;; them with its own float printer (see
  ;;; dev-docs/SCHEME_BACKEND_GAPS.md).
  ;;;
  ;;; The argument is `any`, so nothing is classified: an unbound
  ;;; variable is a *success* that renders as `_`, exactly as the
  ;;; reference's `valueToTerm` does for a variable with no alias. The
  ;;; procedure is therefore fixed at one argument and needs no
  ;;; session.
  (define (%write-term-to-string v)
    (pretty-term v))

  ;;; ---------------------------------------------------------------------
  ;;; print_store / write_store_to_list
  ;;;
  ;;; The two meta primitives that expose the store, ports of
  ;;; `print_store` and `write_store_to_list` in `YCHR.Internal.Meta`.
  ;;; Both are built on `getAllStoredConstraints`
  ;;; (`YCHR.Internal.Runtime.Store`): every constraint type in index
  ;;; order, every suspension of a type in store order, dead ones
  ;;; filtered out. `%make-session` supplies the type names.
  ;;; ---------------------------------------------------------------------

  ;;; The source name of a constraint type, in the compiler's mangled
  ;;; `vmName` form, or the `c#type_N` fallback `constraintTypeLabel`
  ;;; uses for a type the session does not know
  ;;; (`YCHR.Internal.Runtime.Interpreter`).
  (define (constraint-type-name s ctype)
    (let ((names (session-type-names s)))
      (if (and (< ctype (vector-length names))
               (vector-ref names ctype))
          (vector-ref names ctype)
          (string-append "c#type_" (number->string ctype)))))

  ;;; Split a mangled vmName into its decoded components, `(module .
  ;;; base)`, with #f for the module of an unqualified name. This is the
  ;;; inverse the printer applies to every functor: split at the first
  ;;; `__` (a source name never contains one), treat a leading `__` — an
  ;;; internal name — as unqualified, and decode each half's `%u`
  ;;; escapes. Its counterpart in `(ychr pretty)` is `unmangle-segments`,
  ;;; which the printer keeps private and which joins the halves;
  ;;; runtime.sls already carries its own `__` split for `%name-base` and
  ;;; `host-bare-name` (neither of which is this one — `%name-base` must
  ;;; leave escapes in place).
  (define (split-mangled-name mangled)
    (let ((sep (find-double-underscore mangled)))
      (if (or (not sep) (zero? sep))
          (cons #f (decode-mangled-name mangled))
          (cons (decode-mangled-name (substring mangled 0 sep))
                (decode-mangled-name
                 (substring mangled (+ sep 2) (string-length mangled)))))))

  ;;; Deep-dereference a value: `deref` at the top, then recursively in
  ;;; every compound's arguments, the port of `deepDeref` in
  ;;; `YCHR.Internal.Meta`. An unbound variable is left in place, so the
  ;;; printer renders it `_`.
  (define (deep-deref v)
    (let ((d (deref v)))
      (if (term? d)
          (make-term (term-functor d) (deep-deref-args (term-args d)))
          d)))

  (define (deep-deref-args args)
    (let* ((n (vector-length args))
           (out (make-vector n)))
      (do ((i 0 (+ i 1))) ((= i n))
        (vector-set! out i (deep-deref (vector-ref args i))))
      out))

  ;;; One stored constraint as the value the reference's
  ;;; `constraintAsValue` builds: the type name applied to its deeply
  ;;; dereferenced arguments, where a qualified type is the surface `:`
  ;;; compound (`m:c(1)`) and not the mangled `m__c` functor a compiled
  ;;; occurrence of the same spelling carries. The reference makes the
  ;;; same choice, so a value from `write_store_to_list` does not unify
  ;;; with the equivalent written term on either backend; see
  ;;; dev-docs/SCHEME_BACKEND_GAPS.md. The name is the caller's, resolved
  ;;; once per type group the way `suspsOfGroup` resolves it.
  (define (constraint-value name susp)
    (let* ((parts (split-mangled-name name))
           (inner (make-term (string->symbol (cdr parts))
                             (deep-deref-args (suspension-args susp)))))
      (if (car parts)
          (make-term (string->symbol ":")
                     (vector (string->symbol (car parts)) inner))
          inner)))

  ;;; Every alive stored constraint, in the reference's order: the
  ;;; constraint type index ascending — the counterpart of the
  ;;; `IntMap.toAscList` over `storeTypeNames` — and store order within a
  ;;; type. Dead suspensions are skipped, as `renderSusp` and
  ;;; `suspAsValue` skip them. Iterates each type's snapshot, the same
  ;;; interface the generated `Foreach` uses.
  (define (stored-constraint-values s)
    (let ((num-types (vector-length (session-store-by-type s))))
      (let loop ((ctype 0) (acc '()))
        (if (>= ctype num-types)
            (reverse acc)
            (let ((name (constraint-type-name s ctype)))
              (let-values (((storage count) (store-snapshot s ctype)))
                (loop
                 (+ ctype 1)
                 (let inner ((slot 0) (acc acc))
                   (if (>= slot count)
                       acc
                       (let ((susp (snapshot-ref storage slot)))
                         (inner
                          (+ slot 1)
                          (if (alive-constraint? susp)
                              (cons (constraint-value name susp) acc)
                              acc))))))))))))

  ;;; write_store_to_list: the whole store as a list of constraint
  ;;; values. The empty store is the empty list, as `valueList []` is on
  ;;; the Haskell side.
  (define (%write-store-to-list s)
    (fold-right %cons (%nil) (stored-constraint-values s)))

  ;;; print_store: one line per alive constraint, in surface syntax,
  ;;; then the unit atom, mirroring `print_store` in
  ;;; `YCHR.Internal.Meta` (which returns `unit`).
  (define (%print-store s)
    (for-each (lambda (v) (display (pretty-term v)) (newline))
              (stored-constraint-values s))
    (%unit))

  ;;; ---------------------------------------------------------------------
  ;;; The search driver
  ;;
  ;;; A port of `YCHR.Internal.Runtime.Search` and
  ;;; `YCHR.Internal.Runtime.Goal`: @solve\/1@, @findall\/2@,
  ;;; @fold_solutions\/4@ and @fail\/0@ from @library(search)@, plus
  ;;; @library(meta)@'s @run_chr_session\/1@ and @run_chr_session_ep\/1@,
  ;;; which are the same driver on a fresh store. See
  ;;; @docs\/reference\/search.md@ for the user-facing contract.
  ;;
  ;;; Search here is /labeling/, not continuation capture. @alt\/1@ is an
  ;;; ordinary CHR constraint with no rules, so telling it leaves it in
  ;;; the store. The driver forks a session, tells the goal, and runs it
  ;;; to quiescence under the ordinary refined semantics; at quiescence
  ;;; it looks for an alive @search:alt@ suspension. None means the state
  ;;; is a solution. Otherwise it takes the oldest one and, for each
  ;;; alternative in turn, kills the choice, tells that alternative's
  ;;; goal, and recurses.
  ;;
  ;;; Two mechanisms undo a branch, split by what a session reference
  ;;; actually holds:
  ;;
  ;;;   * The snapshot half: the store's growable counts, the store index
  ;;;     pointer, the propagation history and the reactivation queue are
  ;;;     handled here. The queue is per session and simply saved and
  ;;;     restored; the rest are shared objects whose writes are trailed
  ;;;     at the mutation choke points.
  ;;;   * The trail half: variable cells, observer lists and suspension
  ;;;     flags, recorded write-by-write in @(ychr trail)@.
  ;;
  ;;; The variable and suspension-id counters are deliberately part of
  ;;; neither: they stay monotonic across backtracking, so an id burned in
  ;;; an abandoned branch is never handed out again.
  ;;
  ;;; Every exit unwinds to the base mark taken when the search was
  ;;; entered — commit included — so the caller's store, its
  ;;; constraints' flags and every variable the search bound are as they
  ;;; were. A commit keeps exactly one thing, the values of the /goal's
  ;;; variables/: the unbound variables reachable from the goal at entry.
  ;;; The driver reads them, fully dereferenced, at the solution; unwinds;
  ;;; and binds each one to the value read, in the calling session, where
  ;;; an enclosing driver can still undo it.
  ;;; ---------------------------------------------------------------------

  ;;; The marker condition @fail/0@ raises to abandon a branch. Distinct
  ;;; from every other runtime error, because the branch handlers catch
  ;;; exactly this and nothing else: a runtime error must escape the whole
  ;;; search rather than fail a branch.
  ;;;
  ;;; It is deliberately *not* a @&chr-inst@ condition. A rule guard is
  ;;; compiled to a @guard@ that catches @chr-inst?@ and answers @#f@, so
  ;;; a failure carrying that marker would be swallowed by a guard and
  ;;; read as "delayed" instead of unwinding to the driver.
  (define-condition-type &search-failure &condition
    make-search-failure-condition search-failure?)

  (define (raise-search-failure)
    (raise (condition (make-search-failure-condition))))

  ;;; The functors @library(search)@'s @step(A)@ constructors carry, in
  ;;; the mangled form a `MakeTerm` produces for a module-qualified name.
  (define step-continue (string->symbol "search__continue"))
  (define step-stop (string->symbol "search__stop"))
  (define step-commit (string->symbol "search__commit"))

  ;;; The `;` functor, built rather than written as a quoted literal: the
  ;;; Scheme reader takes a semicolon for a comment start even inside a
  ;;; quote, so there is no literal spelling for this symbol.
  (define semicolon-functor (string->symbol ";"))

  ;;; How a goal's constraint names are resolved.
  ;;;
  ;;;   * `'exported-only` — through the program's exports, the way a
  ;;;     caller-supplied goal has to be: a name the caller could not have
  ;;;     written by hand is a caller error.
  ;;;   * `'any-declared` — by qualified name alone. A choice point's
  ;;;     alternatives are often disjuncts lifted out of a `;`, which are
  ;;;     module-internal and exported by nobody, so the export check
  ;;;     would reject exactly the goals the compiler itself generated.

  ;;; The elements of a proper list, or `#f` when the value is not a list
  ;;; at all. The deref-aware counterpart of `fromValueList` in the
  ;;; Haskell registry, mirroring `listElems`.
  (define (list-elems v)
    (let ((d (deref v)))
      (cond
        ((%nil? d) '())
        ((%cons? d)
         (let ((rest (list-elems (get-arg d 1))))
           (and rest (cons (get-arg d 0) rest))))
        (else #f))))

  ;;; A proper runtime list from a Scheme list of values.
  (define (%list-from-list xs)
    (fold-right %cons (%nil) xs))

  ;;; Decompose a goal argument into `(functor arity args)` tells,
  ;;; resolving each name up front. A list value means several goals in
  ;;; order; anything else is a single goal.
  (define (goal-tells s scope who v)
    (let ((elems (list-elems v)))
      (if elems
          (apply append (map (lambda (g) (one-goal s scope who g)) elems))
          (one-goal s scope who v))))

  ;;; One goal. A `;` compound becomes a tell of `search:alt` over its
  ;;; flattened alternatives, so a disjunction reaches the driver as an
  ;;; ordinary choice point; anything else is a single constraint.
  (define (one-goal s scope who v)
    (let ((d (deref v)))
      (if (and (term? d)
               (eq? (term-functor d) semicolon-functor)
               (= (vector-length (term-args d)) 2))
          (let ((alts (semicolon-alts d)))
            (require-tell-proc s who 'search__alt 1)
            (let ((built (%list-from-list alts)))
              (list (list 'search__alt 1 (list built)))))
          (list (goal-constraint s scope who d)))))

  ;;; Flatten the right spine of a `;` compound. `;` is xfy, so
  ;;; `(a ; b ; c)` is a right-nested pair of semicolon compounds and
  ;;; yields three alternatives. A left-nested `((a ; b) ; c)` keeps its
  ;;; left operand as a single alternative, which is itself a disjunctive
  ;;; goal and becomes a nested choice point — the same solution order
  ;;; either way.
  (define (semicolon-alts v)
    (let ((d (deref v)))
      (if (and (term? d)
               (eq? (term-functor d) semicolon-functor)
               (= (vector-length (term-args d)) 2))
          (cons (get-arg d 0) (semicolon-alts (get-arg d 1)))
          (list d))))

  ;;; One goal: a compound or atom whose functor names a constraint.
  ;;; Arguments are passed through untouched so unbound out-variables
  ;;; reach the forked session live.
  ;;;
  ;;; A goal is never a list cell or the empty list: one here means an
  ;;; improper list slipped past `list-elems`, which has to fail as a
  ;;; malformed goal rather than resolve as a constraint named `.`.
  (define (goal-constraint s scope who v)
    (let* ((d (deref v))
           (f (cond ((or (%nil? d) (%cons? d)) #f)
                    ((term? d) (term-functor d))
                    ((symbol? d) d)
                    (else #f))))
      (if f
          (let* ((args (if (term? d) (vector->list (term-args d)) '()))
                 (arity (length args))
                 (resolved (resolve-goal s scope who f arity)))
            (list resolved arity args))
          (%chr-error
           (string-append
            who ": goal must be a constraint term or a list of them")))))

  ;;; Resolve a goal functor to its qualified constraint name and check
  ;;; that the tell procedure exists. Failing here — rather than inside
  ;;; the forked session — keeps "unknown constraint" a caller error.
  (define (resolve-goal s scope who f arity)
    (let ((resolved (if (and (eq? scope 'any-declared)
                             (qualified-functor? f))
                        f
                        (resolve-export s who f arity))))
      (require-tell-proc s who resolved arity)
      resolved))

  ;;; Is this mangled functor already module-qualified? A qualified name
  ;;; embeds the module and the base separated by `__`, and its mangling
  ;;; never introduces one of its own (non-ASCII is escaped as
  ;;; `%%uNNNNNN`), so any occurrence of `__` not at the very start marks
  ;;; a qualified functor. A leading `__` is a compiler-internal name
  ;;; (`__lambda_3`, a lifted disjunct), which is unqualified.
  (define (qualified-functor? f)
    (let* ((s (symbol->string f))
           (sep (find-double-underscore s)))
      (and sep (not (zero? sep)))))

  ;;; Resolve an unqualified (or explicitly qualified) goal name, the way
  ;;; `resolveByExport` does on the Haskell side. Every error here is the
  ;;; caller's: it names a constraint the program cannot reach from this
  ;;; goal.
  (define (resolve-export s who f arity)
    (let ((text (symbol->string f)))
      (if (qualified-functor? f)
          (if (hashtable-contains? (session-exported-goals s) (cons f arity))
              f
              (%chr-error
               (string-append
                who ": Constraint not exported: "
                (readable-functor f) "/" (number->string arity))))
          (let ((target (hashtable-ref (session-short-exports s)
                                       (cons f arity) #f)))
            (cond
              ((not target)
               (%chr-error
                (string-append
                 who ": Unknown constraint: "
                 text "/" (number->string arity))))
              ((symbol? target) target)
              ((pair? target)
               (%chr-error
                (string-append
                 who ": Ambiguous constraint: "
                 text "/" (number->string arity)
                 ", exported by: "
                 (fold-left
                  (lambda (acc m)
                    (if (null? acc) m (string-append acc ", " m)))
                  ""
                  target))))
              (else
               (%chr-error
                (string-append
                 who ": Unknown constraint: "
                 text "/" (number->string arity)))))))))

  ;;; A mangled functor in the form a diagnostic prints it: the module
  ;;; and base of a qualified name joined by `:`, escapes decoded.
  (define (readable-functor f)
    (let* ((s (symbol->string f))
           (sep (find-double-underscore s)))
      (if (or (not sep) (zero? sep))
          (decode-mangled-name s)
          (string-append
           (decode-mangled-name (substring s 0 sep))
           ":"
           (decode-mangled-name
            (substring s (+ sep 2) (string-length s)))))))

  ;;; Check that a resolved constraint has a tell procedure in this
  ;;; program, so a missing one is reported against the goal rather than
  ;;; as a bare procedure-lookup failure later on.
  (define (require-tell-proc s who name arity)
    (unless (hashtable-contains? (session-goals s) (cons name arity))
      (%chr-error
       (string-append
        who ": constraint not found: "
        (readable-functor name)
        "/"
        (number->string arity)))))

  ;;; The unbound variables reachable from the goal at entry, distinct
  ;;; and outermost first: the only thing a commit keeps. The same walk
  ;;; `%term-variables` performs, and a variable already bound when the
  ;;; walk reaches it is dereferenced through, exactly as `collectVars`
  ;;; does on the Haskell side. Collected in the calling session, before
  ;;; the fork exists, so nothing the goal does can change the set.
  (define (prepare-search goals)
    (let ((seen (make-eqv-hashtable))
          (vars '()))
      (define (walk v)
        (let ((d (deref v)))
          (cond
            ((var? d)
             (unless (hashtable-contains? seen (var-id d))
               (hashtable-set! seen (var-id d) #t)
               (set! vars (cons d vars))))
            ((term? d) (vector-for-each walk (term-args d))))))
      (for-each (lambda (g) (for-each walk (car (cddr g)))) goals)
      (reverse vars)))

  ;;; Run a branch, mapping a failure to an outcome. Only the failure
  ;;; marker is caught: a runtime error is not a failure and must escape
  ;;; the search.
  (define (with-failures-caught thunk)
    (guard (c ((search-failure? c) (cons 'failed #f)))
      (cons 'ok (thunk))))

  ;;; The one session reference a branch saves that is neither on the
  ;;; trail nor part of the store: the reactivation queue. It is per
  ;;; session — the caller's pending reactivations stay with the caller —
  ;;; so putting the two halves back restores it exactly.
  (define (begin-queue s)
    (cons (session-queue-front s) (session-queue-back s)))

  (define (use-queue! s saved)
    (session-queue-front-set! s (car saved))
    (session-queue-back-set! s (cdr saved)))

  ;;; The choice point at or after `cursor` in the `alt` type's bucket:
  ;;; `(suspension . slot)`, or `#f` when the state is quiescent.
  ;;;
  ;;; The bucket is read as its storage vector plus its count rather than
  ;;; as a list. That is load-bearing for complexity, not just for style:
  ;;; building the suffix list at every quiescence would make a search
  ;;; path of depth k cost k list steps per quiescence, which is the
  ;;; quadratic behaviour `test/golden/search_deep` exists to catch.
  ;;;
  ;;; Skipping the prefix below `cursor` is not an optimization the caller
  ;;; may get wrong. At every quiescence in the subtree entered on the
  ;;; choice at slot i, every entry below i + 1 is dead or not this
  ;;; search's: the ones in [cursor, i) because this scan read them dead,
  ;;; the ones below cursor by the same property one level up, and i
  ;;; itself because taking the choice kills it. Nothing in that subtree
  ;;; can revive one — a suspension's alive flag only goes back on by
  ;;; trail undo, and every undo reachable from inside the subtree is to
  ;;; a mark taken at or after it was entered.
  (define (find-choice s cursor)
    (let ((ctype (session-alt-type s)))
      (if (not ctype)
          #f
          (let-values (((storage count) (store-snapshot s ctype)))
            (let loop ((slot cursor))
              (if (>= slot count)
                  #f
                  (let ((susp (snapshot-ref storage slot)))
                    (if (and (alive-constraint? susp)
                             (= (vector-length (suspension-args susp)) 1))
                        (cons susp slot)
                        (loop (+ slot 1))))))))))

  ;;; Read `alt(Goals)`. An argument that is not a proper list is a
  ;;; runtime error, not a failure: it is a malformed choice point rather
  ;;; than a dead end.
  (define (choice-goals susp)
    (let ((elems (list-elems (suspension-arg susp 0))))
      (if elems
          elems
          (%chr-error
           "alt/1: argument must be a proper list of alternative goals"))))

  ;;; Explore from the current, quiescent state, looking for choice
  ;;; points from `cursor` onwards. `at-solution` is called, with no
  ;;; arguments, at each quiescent state with no choice left — a solution.
  (define (search-from s cursor at-solution)
    (let ((choice (find-choice s cursor)))
      (if (not choice)
          (at-solution)
          (try-alternatives s
                            (car choice)
                            (cdr choice)
                            (choice-goals (car choice))
                            at-solution))))

  ;;; Tell one resolved goal: the tell procedure the driver looked up.
  ;;; `who` prefixes the error for a goal that got this far unregistered.
  (define (tell-goal s name arity args who)
    (let ((entry (hashtable-ref (session-goals s) (cons name arity) #f)))
      (if entry
          (apply (car entry) s args)
          (%chr-error
           (string-append
            who ": constraint not found: "
            (readable-functor name)
            "/"
            (number->string arity))))))

  ;;; Try each alternative of one choice point in list order, undoing the
  ;;; branch between attempts.
  ;;;
  ;;; Contract: this answers either the value the solution handler
  ;;; returned, or the symbol `failed`. `with-failures-caught` already
  ;;; turns an abandoned branch into `failed`, so the single check below
  ;;; covers both "the branch failed" and "the handler asked for the next
  ;;; solution" — which is what makes every enclosing alternative level
  ;;; undo and try its next one too.
  (define (try-alternatives s susp slot goals at-solution)
    (if (null? goals)
        'failed
        (let* ((goal (car goals))
               (mark (trail-mark))
               (queue (begin-queue s))
               (branch
                (with-failures-caught
                 (lambda ()
                   ;; Taking the choice consumes it: an alternative must
                   ;; not rediscover its own choice point and recurse
                   ;; forever. The kill is trailed like any other flag
                   ;; write, so the constraint is alive again if this
                   ;; alternative is abandoned.
                   (kill-constraint susp)
                   ;; Resolved here, inside the branch, and without the
                   ;; export check: a lifted disjunct is a
                   ;; module-internal constraint, so the check that
                   ;; guards a caller-supplied goal would reject exactly
                   ;; the goals the compiler generated.
                   (for-each
                    (lambda (g)
                      (tell-goal s (car g) (cadr g) (car (cddr g)) "alt"))
                    (goal-tells s 'any-declared "alt" goal))
                   ;; Past this choice, not from the front: this one is
                   ;; killed just above. Each alternative gets the same
                   ;; starting point, because the undo below puts the
                   ;; bucket back exactly as it was.
                   (search-from s (+ slot 1) at-solution))))
               (value (if (eq? (car branch) 'ok) (cdr branch) 'failed)))
          (if (eq? value 'failed)
              (begin
                (use-queue! s queue)
                (trail-unwind! mark)
                (try-alternatives s susp slot (cdr goals) at-solution))
              value))))

  ;;; A value with every bound variable replaced by what it is bound to,
  ;;; all the way down. Unbound variables stay themselves. Does not
  ;;; terminate on a cyclic term (unification has no occurs check), like
  ;;; `%copy-term` and the goal-variable walk.
  (define (resolve-value v)
    (let ((d (deref v)))
      (if (term? d)
          (let* ((args (term-args d))
                 (n (vector-length args))
                 (out (make-vector n)))
            (do ((i 0 (+ i 1))) ((= i n))
              (vector-set! out i (resolve-value (vector-ref args i))))
            (make-term (term-functor d) out))
          d)))

  ;;; Fork a search session, tell the already-resolved goal, and drive it.
  ;;;
  ;;; Returns the pair `(outcome . kept)` where `outcome` is `'committed`,
  ;;; `'stopped` or `'exhausted`, and `kept` is the goal variables' values
  ;;; in the solution — read before the unwind — or `#f`.
  ;;;
  ;;; Every exit — a commit, a `stop` step, exhaustion, or an escaping
  ;;; runtime error — unwinds the search to the mark taken here before
  ;;; returning or rethrowing. A caller that catches the error
  ;;; (`%run-chr-session`, which turns it into `#f`) therefore resumes
  ;;; with the bindings it had, the way ISO `catch/3` does.
  (define (drive-search s mode goal-vars goals on-solution)
    (let* ((sub (%fork-session s mode))
           (prev (trail-enter!))
           (base (trail-mark))
           (ctype (session-alt-type sub))
           ;; Only the choice points this search tells are its own, so the
           ;; cursor starts past the caller's — which may hold pending
           ;; choices of an enclosing driver, or an inert `alt` told
           ;; outside any search. A `'fresh` fork starts from an empty
           ;; store, so its count is 0 in either reading.
           (cursor (if ctype
                       (let-values
                           (((storage count) (store-snapshot sub ctype)))
                         count)
                       0))
           (kept #f))
      ;; Answers the symbol `failed` when the handler asked for the next
      ;; solution, which makes the enclosing alternative undo and move on,
      ;; and `stopped` or `committed` to end the search.
      (define (at-solution)
        (let ((decision (on-solution)))
          (cond
            ((eq? decision 'continue) 'failed)
            ((eq? decision 'stop) 'stopped)
            ((eq? decision 'commit)
             ;; Read before the unwind below takes the solution away.
             (set! kept (map resolve-value goal-vars))
             'committed)
            (else
             (%chr-error
              (string-append
               "fold_solutions: the step function must return continue/1,"
               " stop/1 or commit/1"))))))
      (define (body)
        (for-each
         (lambda (g)
           (tell-goal sub (car g) (cadr g) (car (cddr g)) "solve"))
         goals)
        (search-from sub cursor at-solution))
      (define (leave)
        (trail-unwind! base)
        (trail-exit! prev))
      ;; Unwind and restore the trail on every exit, including one that
      ;; escapes as a condition: the trail must not stay active for the
      ;; caller, or its next `%fail` would report an enclosing search that
      ;; is not there. Conditions are the only non-local exit to cover:
      ;; the generated code's `call/cc` escapes never leave the procedure
      ;; that captured them, so none crosses this host call.
      (let ((result
             (guard (c (#t (leave) (raise c)))
               (with-failures-caught body))))
        (leave)
        (if (not (eq? (car result) 'ok))
            (cons 'exhausted #f)
            (let ((r (cdr result)))
              (if (eq? r 'committed)
                  (cons 'committed kept)
                  (cons (if (eq? r 'stopped) 'stopped 'exhausted)
                        #f)))))))

  ;;; Reject a commit that would bind a goal variable a live stored
  ;;; constraint of the calling session observes. A commit binds goal
  ;;; variables outside any rule body, so nothing would reactivate that
  ;;; constraint and its rules would silently miss the new value. A search
  ;;; that does not commit binds nothing, so it is never checked: that is
  ;;; what lets @findall@ label a variable the caller's store constrains.
  ;;;
  ;;; An observer owned by another session's store is foreign and a dead
  ;;; or unstored one is stale; neither counts. An inert constraint
  ;;; registers no observers at all, so it does not count either.
  (define (watchful? owner obs)
    (cond
      ((null? obs) #f)
      ((and (suspension-alive? (car obs))
            (suspension-stored? (car obs))
            (eq? (suspension-owner (car obs)) owner))
       #t)
      (else (watchful? owner (cdr obs)))))

  (define (check-unwatched who owner vars)
    (for-each
     (lambda (v)
       (let ((d (deref v)))
         (when (and (var? d) (watchful? owner (var-observers d)))
           (%chr-error
            (string-append
             who
             ": goal variable is observed by a stored constraint;"
             " pass a fresh variable and unify after the call")))))
     vars))

  ;;; The second half of a commit, in the calling session once the search
  ;;; has unwound: check that no goal variable is watched
  ;;; (`check-unwatched`), then bind each one to its value in the
  ;;; solution. A no-op when the search did not commit.
  ;;;
  ;;; Run outside `%run-chr-session`'s catch, so a watched goal variable
  ;;; is a loud caller error from every entry point, never a `#f`. The
  ;;; observers `unify` returns are dropped: the check ruled out a live
  ;;; one, and this is not a rule body, so there is no drain to hand them
  ;;; to.
  (define (commit-goal-vars s who vars kept)
    (when kept
      (check-unwatched who (session-owner s) vars)
      (for-each
       (lambda (var val)
         (let-values (((ok obs) (unify var val)))
           (unless ok
             (%chr-error
              (string-append
               who ": rebinding a goal variable failed")))))
       vars
       kept)))

  ;;; Resolve the goal, collect its variables, and drive it: the decode
  ;;; and the collection happen in the calling session, before the fork
  ;;; exists, so an unknown goal constraint is a caller error and never a
  ;;; failed branch.
  (define (run-search s who mode goal on-solution)
    (let* ((goals (goal-tells s 'exported-only who goal))
           (vars (prepare-search goals))
           (result (drive-search s mode vars goals on-solution))
           (outcome (car result))
           (kept (cdr result)))
      (commit-goal-vars s who vars kept)
      outcome))
  ;;; @solve(Goal)@: run @Goal@ against a fork of the caller's store and
  ;;; stop at its first solution. Commits: the goal's variables are bound
  ;;; to their values in the solution, and nothing else is kept. @#f@ when
  ;;; the space is exhausted, with everything undone.
  (define (%solve s g)
    (eq? (run-search s "solve" 'copy g (lambda () 'commit))
         'committed))

  ;;; @run_chr_session_ep(Goal)@: @solve/1@ on a fresh, empty session
  ;;; instead of a fork of the caller's store. Errors propagate.
  (define (%run-chr-session-ep s g)
    (eq? (run-search s "run_chr_session_ep" 'fresh g (lambda () 'commit))
         'committed))

  ;;; @run_chr_session(Goal)@: @%run-chr-session-ep@ made total.
  ;;;
  ;;; Same fresh session, same base mark, same commit-on-first-solution —
  ;;; the one difference is that a runtime error escaping @Goal@ becomes
  ;;; @#f@ instead of propagating. That makes this the language's only
  ;;; error catcher, which is the whole reason it is a host call rather
  ;;; than written in CHR over @run_chr_session_ep@.
  ;;;
  ;;; Only an error is caught. A failure — from @fail/0@ in the goal, or
  ;;; from an exhausted choice point — never reaches here:
  ;;; `with-failures-caught` inside `drive-search` absorbs it into
  ;;; `'exhausted`, which is @#f@ by the same rule.
  (define (%run-chr-session s g)
    (let* ((goals (goal-tells s 'exported-only "run_chr_session" g))
           (vars (prepare-search goals))
           (outcome #f)
           (kept #f))
      ;; Resolved and prepared above, and committed below, rather than
      ;; inside the catch: a misspelled or unexported goal constraint, or
      ;; a commit onto a watched goal variable, stays a loud caller error
      ;; instead of being swallowed into a `#f`.
      (guard (c ((or (error? c) (serious-condition? c))
                 (set! outcome 'exhausted)))
        ;; `drive-search` answers ONE value, the pair `(outcome . kept)`;
        ;; destructuring it as multiple values would raise, and the guard
        ;; above would turn that into a silent `#f`.
        (let ((result
               (drive-search s 'fresh vars goals (lambda () 'commit))))
          (set! outcome (car result))
          (set! kept (cdr result))))
      (commit-goal-vars s "run_chr_session" vars kept)
      (eq? outcome 'committed)))

  ;;; @findall(Template, Goal)@: every solution of @Goal@, as a list of
  ;;; copies of @Template@ in search order.
  ;;;
  ;;; The copies are what survive: the search is fully unwound
  ;;; afterwards, so no binding it made is visible to the caller. The
  ;;; accumulator is an ordinary Scheme variable, which backtracking does
  ;;; not roll back — the trail covers variable cells and suspension flags
  ;;; and nothing else.
  (define (%findall s template g)
    (let ((acc '()))
      (run-search
       s
       "findall"
       'copy
       g
       (lambda ()
         (set! acc (cons (%copy-term s template) acc))
         ;; Never stop: asking for the next solution backtracks out of
         ;; this one.
         'continue))
      ;; `acc` is newest-first, so reversing it (in the accumulator, not in
      ;; the trail-covered cells) yields search order.
      (fold-right %cons (%nil) (reverse acc))))

  ;;; @fold_solutions(Template, Goal, F, Acc0)@: fold @F@ over the
  ;;; solutions of @Goal@, in search order, with the fold in control of
  ;;; when to stop.
  ;;;
  ;;; At each solution @F@ is applied to a copy of @Template@ and the
  ;;; accumulator, and answers with a @step(A)@: @continue@ asks for the
  ;;; next solution, @stop@ ends the search and undoes everything,
  ;;; @commit@ ends it and keeps the solution's values of the goal's
  ;;; variables.
  ;;;
  ;;; The witness is copied and the accumulator is not; see
  ;;; @docs\/reference\/search.md@, "What the fold may carry".
  (define (%fold-solutions s template g f acc0)
    (let ((acc acc0))
      (run-search
       s
       "fold_solutions"
       'copy
       g
       (lambda ()
         (let* ((copied (%copy-term s template))
                (result (%apply-closure s f copied acc))
                (step (read-step result)))
           (set! acc (cdr step))
           (car step))))
      acc))

  ;;; Read the @step(A)@ a fold's step function returned, as `(step .
  ;;; accumulator)`. Anything else is a runtime error: a fold whose step
  ;;; function answers with a bare value has no way to say what to do
  ;;; next.
  (define (read-step v)
    (let ((d (deref v)))
      (if (and (term? d)
               (= (vector-length (term-args d)) 1)
               (memq (term-functor d)
                     (list step-continue step-stop step-commit)))
          (cons (cond ((eq? (term-functor d) step-continue) 'continue)
                      ((eq? (term-functor d) step-stop) 'stop)
                      (else 'commit))
                (get-arg d 0))
          (%chr-error
           (string-append
            "fold_solutions: the step function must return continue/1,"
            " stop/1 or commit/1, got "
            (pretty-term d))))))

  ;;; @fail()@: abandon the current branch.
  ;;;
  ;;; The trail doubles as the "is a search running?" flag, since a search
  ;;; entry point installs it and nothing else does. Outside a search
  ;;; there is no branch to fail, so this is a loud runtime error rather
  ;;; than a silent success or a stuck query.
  (define (%fail s)
    (if (trail-active?)
        (raise-search-failure)
        (%chr-error
         "fail/0 outside a search: no enclosing search entry point")))


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
