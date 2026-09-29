;;; Chez Scheme launcher for the YCHR Scheme backend benchmarks.
;;;
;;; The counterpart of run-guile.scm: same shared harness, Chez's clock.
;;; `(current-time 'time-monotonic)` gives a monotonic nanosecond
;;; reading, which is what a benchmark wants; the accessors live in
;;; `(chezscheme)` and are imported with `only` because importing that
;;; library next to `(rnrs)` fails with a multiple-definitions error.
;;;
;;; Run it through the Makefile:
;;;
;;;   make bench-scheme-chez
;;;   make bench-scheme-chez SCHEME_BENCH_ARGS="--quick --only fib"
;;;
;;; or directly, after `make bench-scheme` has compiled the programs:
;;;
;;;   scheme --libdirs bench/scheme:scheme:dist-scheme-bench \
;;;          --libexts .sls --program bench/scheme/run-chez.scm
;;;
;;; (Arguments for the harness go after `--`: Chez rejects unknown
;;; options before it, and passes the bare `--` through to
;;; `command-line`, which the harness ignores.)
(import (rnrs base) (rnrs io simple) (rnrs programs)
        (only (chezscheme) current-time time-second time-nanosecond)
        (bench harness))

(define (chez-now)
  (let ((t (current-time 'time-monotonic)))
    (+ (* (time-second t) 1000000000) (time-nanosecond t))))

(display "YCHR Scheme benchmarks [Chez Scheme]") (newline)
(exit (run-all (command-line) chez-now 1000000000))
