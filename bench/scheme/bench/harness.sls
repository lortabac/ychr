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
            bench_maplist:go/2))

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

  (define (measure now ticks-per-sec thunk)
    (let loop ((i 0) (ts '()) (elapsed 0.0))
      (if (and (>= i min-iters) (or (>= elapsed budget-ms) (>= i max-iters)))
          (stats (reverse ts))
          (let* ((t0 (now))
                 (ignored (thunk))
                 (t1 (now))
                 (ms (to-ms ticks-per-sec (- t1 t0))))
            (loop (+ i 1) (cons ms ts) (+ elapsed ms))))))

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
  ;; The benchmark programs
  ;; ------------------------------------------------------------------

  (define (cases)
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
        (lambda (r) (equal? r 41541750)))))

  ;; ------------------------------------------------------------------
  ;; Driver
  ;; ------------------------------------------------------------------

  (define (header)
    (display (pad-right "case" 16))
    (display (pad-left "n" 8))
    (display (pad-left "min ms" 11))
    (display (pad-left "median ms" 12))
    (display (pad-left "mean ms" 11))
    (display (pad-left "max ms" 11))
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

  (define (run-one c now ticks-per-sec)
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
        (let ((row (measure now ticks-per-sec thunk)))
          (display (pad-right name 16))
          (display (pad-left (number->string (list-ref row 0)) 8))
          (display (pad-left (num (list-ref row 1)) 11))
          (display (pad-left (num (list-ref row 2)) 12))
          (display (pad-left (num (list-ref row 3)) 11))
          (display (pad-left (num (list-ref row 4)) 11))
          ;; The check runs once, untimed, after the measurement.
          (let ((ok (if check (check (thunk)) #t)))
            (display (if ok "  ok    " "  FAIL  "))
            (display (bench-case-detail c))
            (newline)
            ok)))))

  (define (run-all argv now ticks-per-sec)
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
         (header)
         (let ((failed
                (fold-left
                 (lambda (n c)
                   (if (or (null? only) (member (bench-case-name c) only))
                       (if (run-one c now ticks-per-sec) n (+ n 1))
                       n))
                 0 all)))
           (if (= failed 0) 0 1))))))
)
