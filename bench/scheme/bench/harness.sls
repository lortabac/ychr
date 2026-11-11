;;;; Shared benchmark harness for the YCHR Scheme backend.
;;;;
;;;; This library is implementation-independent: it names no clock and no
;;;; interpreter-specific binding. The launchers `run-guile.scm` and
;;;; `run-chez.scm` supply a clock (`now` plus ticks-per-second) and an
;;;; exit status, and are the only files that know which implementation
;;;; is running.
;;;;
;;;; Each measured iteration creates a *fresh* session and runs one
;;;; workload — telling a goal, or (for the `session` case) only creating
;;;; the session — mirroring what `bench/Main.hs` measures on the Haskell
;;;; side (`runGoalConstraint` rebuilds the session per call).
;;;; Compilation happens once in the Makefile and is excluded, as are
;;;; process startup and library loading.
;;;;
;;;; The import set below is the portable subset of R6RS that both Guile 3
;;;; and Chez Scheme provide. Notes, all verified by running both:
;;;;
;;;;   * `do` needs (rnrs control); `define-record-type` needs
;;;;     (rnrs records syntactic); `condition-message` needs
;;;;     (rnrs conditions).
;;;;   * Use `div`, not `quotient`: `quotient` is unbound in Chez's (rnrs).
;;;;   * Use `inexact`, not `exact->inexact`: unbound in Chez's (rnrs).
;;;;   * The record type is named `bench-case` rather than `case`, which
;;;;     would shadow the `case` syntax.
;;;;   * Do not import bare (rnrs): it emits "overrides core binding"
;;;;     warnings on Guile.
(library (bench harness)
  (export run-all)
  (import (rnrs base) (rnrs exceptions) (rnrs conditions) (rnrs control)
          (rnrs records syntactic) (rnrs io simple)
          (rnrs sorting) (rnrs lists)
          (ychr runtime)
          (only (ychr generated bench_fib) bench_fib fib:fib/2)
          (only (ychr generated bench_guard) bench_guard guard:clamp/3)
          (only (ychr generated bench_graph) bench_graph graph_test:run/3)
          (only (ychr generated bench_leqc) bench_leqc leqc:run/1)
          (only (ychr generated bench_list) bench_list bench_list:go/2)
          (only (ychr generated bench_maplist) bench_maplist
            bench_maplist:go/2)
          (only (ychr generated bench_sum) bench_sum bench_sum:go/2)
          (only (ychr generated bench_terms) bench_terms bench_terms:go/2)
          (prefix (bench expr-native) n:)
          (prefix (ychr types bench_expr) d:)
          (prefix (ychr ground-types bench_expr) g:))

  ;; ------------------------------------------------------------------
  ;; Measurement policy
  ;;
  ;; Iteration counts are adaptive rather than fixed: Chez Scheme is two
  ;; to three orders of magnitude faster than Guile on these workloads,
  ;; so a count tuned for one implementation is either a blink or
  ;; minutes of work on the other. A case runs at least `min-iters`
  ;; timed iterations and keeps going until `budget-ms` of wall time has
  ;; accumulated, capped at `max-iters`. `warmup` untimed iterations run
  ;; first.
  ;; ------------------------------------------------------------------
  (define budget-ms 150.0)
  (define min-iters 3)
  (define max-iters 200000)
  (define warmup 2)

  ;; One benchmark case: `detail` is the goal text shown in the table;
  ;; `thunk` runs the workload and returns a result; `check` is #f, or a
  ;; predicate applied to that result once, untimed, after the
  ;; measurement. Every case carries a check, because a benchmark that
  ;; has silently stopped doing its work is otherwise indistinguishable
  ;; from a fast one.
  (define-record-type (bench-case make-bench-case bench-case?)
    (fields name detail thunk check))

  ;; ------------------------------------------------------------------
  ;; Statistics and formatting
  ;; ------------------------------------------------------------------

  (define (to-ms ticks-per-sec ticks)
    (inexact (/ (* 1000 ticks) ticks-per-sec)))

  ;; (n min median mean max)
  (define (stats ts)
    (let* ((sorted (list-sort < ts)) (n (length sorted)))
      (list n
            (car sorted)
            (list-ref sorted (div n 2))
            (/ (fold-left + 0 sorted) n)
            (list-ref sorted (- n 1)))))

  ;; The stats row, plus the mean bytes allocated per iteration when
  ;; `alloc` (a thunk giving the total bytes allocated so far) is given.
  (define (measure now ticks-per-sec thunk alloc)
    (let loop ((i 0) (ts '()) (elapsed 0.0) (b0 (and alloc (alloc))))
      (if (and (>= i min-iters) (or (>= elapsed budget-ms) (>= i max-iters)))
          (append (stats (reverse ts))
                  (list (and alloc (div (- (alloc) b0) i))))
          (let* ((t0 (now))
                 (ignored (thunk))
                 (t1 (now))
                 (ms (to-ms ticks-per-sec (- t1 t0))))
            (loop (+ i 1) (cons ms ts) (+ elapsed ms) b0)))))

  ;; Live constraints of one type in a session. The store is append-only,
  ;; so the snapshot's count includes killed constraints; a store-size
  ;; check wants the live ones.
  (define (live-count s ctype)
    (let-values (((storage count) (store-snapshot s ctype)))
      (let loop ((i 0) (live 0))
        (if (= i count)
            live
            (loop (+ i 1)
                  (if (suspension-alive? (snapshot-ref storage i))
                      (+ live 1)
                      live))))))

  (define (pad-left s w)
    (let ((k (- w (string-length s))))
      (if (<= k 0) s (string-append (make-string k #\space) s))))

  (define (pad-right s w)
    (let ((k (- w (string-length s))))
      (if (<= k 0) s (string-append s (make-string k #\space)))))

  ;; Two decimals, trailing zeros trimmed by number->string.
  (define (num x)
    (number->string (inexact (/ (round (* 100 x)) 100))))

  ;; ------------------------------------------------------------------
  ;; Expression trees read through a types library
  ;;
  ;; The same client code over three libraries with one interface: the
  ;; one `ychr scheme-types` writes (`deref`), the one it writes with
  ;; `--ground` (`ground`), and native records (`native`, the
  ;; reference). The macro spells each procedure name out, so every call
  ;; goes straight to the library's binding, as in a real client.
  ;; ------------------------------------------------------------------

  (define-syntax define-expr-client
    (syntax-rules ()
      ((_ (build size rewrite)
          (make-lit lit? lit-1) (make-neg neg? neg-1)
          (make-add add? add-1 add-2) (make-mul mul? mul-1 mul-2)
          (make-ifz ifz? ifz-1 ifz-2 ifz-3))
       (begin
         ;; A tree of depth `d`, the shape picked by `d mod 5`.
         (define (build d)
           (if (= d 0)
               (make-lit 1)
               (case (mod d 5)
                 ((0) (make-neg (build (- d 1))))
                 ((1) (make-add (build (- d 1)) (build (- d 1))))
                 ((2) (make-mul (build (- d 1)) (make-lit d)))
                 ((3) (make-ifz (make-lit 0) (build (- d 1)) (make-lit d)))
                 (else (make-add (build (- d 1)) (build (- d 1)))))))
         ;; Node count.
         (define (size e)
           (cond ((lit? e) 1)
                 ((neg? e) (+ 1 (size (neg-1 e))))
                 ((add? e) (+ 1 (size (add-1 e)) (size (add-2 e))))
                 ((mul? e) (+ 1 (size (mul-1 e)) (size (mul-2 e))))
                 ((ifz? e) (+ 1 (size (ifz-1 e)) (size (ifz-2 e))
                              (size (ifz-3 e))))
                 (else (error 'size "not an expr" e))))
         ;; A new tree, with add and mul swapped.
         (define (rewrite e)
           (cond ((lit? e) (make-lit (lit-1 e)))
                 ((neg? e) (make-neg (rewrite (neg-1 e))))
                 ((add? e) (make-mul (rewrite (add-1 e)) (rewrite (add-2 e))))
                 ((mul? e) (make-add (rewrite (mul-1 e)) (rewrite (mul-2 e))))
                 ((ifz? e) (make-ifz (rewrite (ifz-1 e)) (rewrite (ifz-2 e))
                                     (rewrite (ifz-3 e))))
                 (else (error 'rewrite "not an expr" e))))))))

  (define-expr-client (n-build n-size n-rewrite)
    (n:make-lit n:lit? n:lit-1) (n:make-neg n:neg? n:neg-1)
    (n:make-add n:add? n:add-1 n:add-2) (n:make-mul n:mul? n:mul-1 n:mul-2)
    (n:make-ifz n:ifz? n:ifz-1 n:ifz-2 n:ifz-3))
  (define-expr-client (d-build d-size d-rewrite)
    (d:make-lit d:lit? d:lit-1) (d:make-neg d:neg? d:neg-1)
    (d:make-add d:add? d:add-1 d:add-2) (d:make-mul d:mul? d:mul-1 d:mul-2)
    (d:make-ifz d:ifz? d:ifz-1 d:ifz-2 d:ifz-3))
  (define-expr-client (g-build g-size g-rewrite)
    (g:make-lit g:lit? g:lit-1) (g:make-neg g:neg? g:neg-1)
    (g:make-add g:add? g:add-1 g:add-2) (g:make-mul g:mul? g:mul-1 g:mul-2)
    (g:make-ifz g:ifz? g:ifz-1 g:ifz-2 g:ifz-3))

  (define expr-depth 40)
  (define expr-nodes 371366)

  ;; build/V, size/V and rewrite/V for one library. The tree the last two
  ;; walk is built once, outside the timing.
  (define (expr-cases v build size rewrite)
    (let ((tree #f))
      (define (the-tree)
        (unless tree (set! tree (build expr-depth)))
        tree)
      (define (nodes? n) (and (= n expr-nodes) (= n (size (the-tree)))))
      (list
        (make-bench-case (string-append "build/" v) "expr tree, depth 40"
          (lambda () (build expr-depth))
          (lambda (t) (nodes? (size t))))
        (make-bench-case (string-append "size/" v) "expr tree, depth 40"
          (lambda () (size (the-tree))) nodes?)
        (make-bench-case (string-append "rewrite/" v) "expr tree, depth 40"
          (lambda () (rewrite (the-tree)))
          (lambda (t) (nodes? (size t)))))))

  ;; ------------------------------------------------------------------
  ;; The benchmark programs
  ;; ------------------------------------------------------------------

  (define (cases)
    (append
     (list
      ;; Session creation alone. Every other case pays a library-specific
      ;; part of this cost, so subtract it only as a rough indication.
      (make-bench-case "session" "(session creation)"
        (lambda () (bench_fib))
        (lambda (s) (session? s)))
      ;; Guard/arithmetic.
      (make-bench-case "guard" "guard:clamp(3,5,R)"
        (lambda ()
          (let* ((s (bench_guard)) (a (make-var s)))
            (guard:clamp/3 s 3 5 a)
            (deref a)))
        (lambda (r) (equal? r 5)))
      ;; Partner search with numeric guards and constraint removal.
      (make-bench-case "graph" "graph_test:run(R1,R2,R3)"
        (lambda ()
          (let* ((s (bench_graph))
                 (a (make-var s)) (b (make-var s)) (c (make-var s)))
            (graph_test:run/3 s a b c)
            (list (deref a) (deref b) (deref c))))
        (lambda (r)
          (and (equal?/chr (list-ref r 0) (make-term 'found (vector 1)))
               (equal?/chr (list-ref r 1) (make-term 'found (vector 2)))
               (equal? (list-ref r 2) 'none))))
      ;; Rule recursion, trail, arithmetic.
      (make-bench-case "fib" "fib:fib(20,R)"
        (lambda ()
          (let* ((s (bench_fib)) (a (make-var s)))
            (fib:fib/2 s 20 a)
            (deref a)))
        (lambda (r) (equal? r 6765)))
      ;; Store growth, partner search, propagation history, reactivation.
      ;; `bench_leqc` declares `gen` before `leq`, so `leq` is constraint
      ;; type 1 here; closing a chain of 20 leaves one live `leq` per pair,
      ;; 20*19/2 = 190.
      (make-bench-case "leq_closure" "leqc:run(20)"
        (lambda ()
          (let ((s (bench_leqc)))
            (leqc:run/1 s 20)
            s))
        (lambda (s) (= (live-count s 1) 190)))
      ;; List construction, recursion, `is` deep evaluation.
      (make-bench-case "list_sum" "bench_list:go(500,R)"
        (lambda ()
          (let* ((s (bench_list)) (a (make-var s)))
            (bench_list:go/2 s 500 a)
            (deref a)))
        (lambda (r) (equal? r 124750)))
      ;; maplist over a lambda: `$call`/closure-table dispatch per element.
      (make-bench-case "maplist" "bench_maplist:go(500,R)"
        (lambda ()
          (let* ((s (bench_maplist)) (a (make-var s)))
            (bench_maplist:go/2 s 500 a)
            (deref a)))
        (lambda (r) (equal? r 41541750)))
      ;; Non-tail user-function recursion: equation dispatch plus the
      ;; prelude arithmetic helpers, with no constraint partner search.
      ;; This is the case that showed the per-call `call/cc` escape.
      (make-bench-case "sum" "bench_sum:go(2000,R)"
        (lambda ()
          (let* ((s (bench_sum)) (a (make-var s)))
            (bench_sum:go/2 s 2000 a)
            (deref a)))
        (lambda (r) (equal? r 2001000)))
      ;; Compound terms of arity 1-4 and 9: construction, head matching
      ;; and argument reads. The case for the term representation.
      (make-bench-case "terms" "bench_terms:go(500,R)"
        (lambda ()
          (let* ((s (bench_terms)) (a (make-var s)))
            (bench_terms:go/2 s 500 a)
            (deref a)))
        (lambda (r) (equal? r 2379750))))
     (expr-cases "native" n-build n-size n-rewrite)
     (expr-cases "deref" d-build d-size d-rewrite)
     (expr-cases "ground" g-build g-size g-rewrite)))

  ;; ------------------------------------------------------------------
  ;; Driver
  ;; ------------------------------------------------------------------

  (define (header alloc)
    (display (pad-right "case" 16))
    (display (pad-left "n" 8))
    (display (pad-left "min ms" 11))
    (display (pad-left "median ms" 12))
    (display (pad-left "mean ms" 11))
    (display (pad-left "max ms" 11))
    (when alloc (display (pad-left "bytes/iter" 12)))
    (display "  check  goal")
    (newline))

  (define (usage script)
    (display "usage: ")
    (display script)
    (display " [--quick] [--only NAME]... [--help]")
    (newline))

  ;; Name from a `--only=NAME` token, or #f.
  (define (only= token)
    (and (> (string-length token) 7)
         (string=? (substring token 0 7) "--only=")
         (substring token 7 (string-length token))))

  ;; Parse the harness arguments into (quick only help bad), where `bad`
  ;; is the first unrecognized or malformed token. A bare `--` is
  ;; tolerated: Chez passes that separator through to `command-line`.
  (define (parse-args args)
    (let loop ((args args) (quick #f) (help #f) (only '()))
      (cond
        ((null? args) (list quick (reverse only) help #f))
        ((string=? (car args) "--") (loop (cdr args) quick help only))
        ((string=? (car args) "--quick") (loop (cdr args) #t help only))
        ((string=? (car args) "--help") (loop (cdr args) quick #t only))
        ((string=? (car args) "--only")
         (if (pair? (cdr args))
             (loop (cddr args) quick help (cons (cadr args) only))
             (list quick (reverse only) help "--only")))
        (else
         (let ((name (only= (car args))))
           (if name
               (loop (cdr args) quick help (cons name only))
               (list quick (reverse only) help (car args))))))))

  (define (unknown-only only valid)
    (cond ((null? only) #f)
          ((member (car only) valid) (unknown-only (cdr only) valid))
          (else (car only))))

  (define (run-one c now ticks-per-sec alloc)
    (let ((name (bench-case-name c))
          (thunk (bench-case-thunk c))
          (check (bench-case-check c)))
      (guard (e (#t
                 (display name)
                 (display "  ERROR: ")
                 (display (condition-message e))
                 (newline)
                 #f))
        (do ((i 0 (+ i 1))) ((= i warmup)) (thunk))
        (let ((row (measure now ticks-per-sec thunk alloc)))
          (display (pad-right name 16))
          (display (pad-left (number->string (list-ref row 0)) 8))
          (display (pad-left (num (list-ref row 1)) 11))
          (display (pad-left (num (list-ref row 2)) 12))
          (display (pad-left (num (list-ref row 3)) 11))
          (display (pad-left (num (list-ref row 4)) 11))
          (when alloc
            (display (pad-left (number->string (list-ref row 5)) 12)))
          ;; The check runs once, untimed, after the measurement.
          (let ((ok (if check (check (thunk)) #t)))
            (display (if ok "  ok    " "  FAIL  "))
            (display (bench-case-detail c))
            (newline)
            ok)))))

  ;; `alloc` is optional: a thunk giving the total bytes allocated so
  ;; far, which adds a bytes-per-iteration column (Chez passes one).
  (define run-all
    (case-lambda
      ((argv now ticks-per-sec) (run-all* argv now ticks-per-sec #f))
      ((argv now ticks-per-sec alloc) (run-all* argv now ticks-per-sec alloc))))

  (define (run-all* argv now ticks-per-sec alloc)
    (let* ((script (if (pair? argv) (car argv) "run-all"))
           (parsed (parse-args (cdr argv)))
           (quick (list-ref parsed 0))
           (only (list-ref parsed 1))
           (help (list-ref parsed 2))
           (bad (list-ref parsed 3))
           (all (cases))
           (valid (map bench-case-name all))
           (unknown (unknown-only only valid)))
      (cond
        (bad
         (display "unknown or malformed argument: ")
         (display bad)
         (newline)
         (usage script)
         1)
        (help (usage script) 0)
        (unknown
         (display "unknown case: ")
         (display unknown)
         (newline)
         (display "valid cases: ")
         (display valid)
         (newline)
         1)
        (else
         (if quick
             (begin
               (set! budget-ms 40.0)
               (set! min-iters 1)
               (set! max-iters 2000)
               (set! warmup 1)))
         (header alloc)
         (let ((failed
                (fold-left
                 (lambda (n c)
                   (if (or (null? only) (member (bench-case-name c) only))
                       (if (run-one c now ticks-per-sec alloc) n (+ n 1))
                       n))
                 0 all)))
           (if (= failed 0) 0 1))))))
)
