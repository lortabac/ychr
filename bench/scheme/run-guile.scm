;;; Guile launcher for the YCHR Scheme backend benchmarks.
;;;
;;; Supplies the clock the shared harness (bench/harness.sls) needs and
;;; turns the harness's failure count into an exit status. `--quick`,
;;; `--only NAME` and `--help` are passed through to the harness.
;;;
;;; Run it through the Makefile:
;;;
;;;   make bench-scheme
;;;   make bench-scheme SCHEME_BENCH_ARGS="--quick --only fib"
;;;
;;; or directly, after `make bench-scheme` has compiled the programs:
;;;
;;;   guile3.0 --r6rs --no-auto-compile \
;;;     -L bench/scheme -L scheme -L dist-scheme-bench -x .sls \
;;;     bench/scheme/run-guile.scm
(import (rnrs base) (rnrs io simple) (rnrs programs) (bench harness))

;; `get-internal-real-time` and `internal-time-units-per-second` are Guile
;; core bindings; both stay visible with the R6RS imports above, and the
;; counter is the highest-resolution clock Guile offers.
(display "YCHR Scheme benchmarks [Guile]") (newline)
(exit (run-all (command-line)
               (lambda () (get-internal-real-time))
               internal-time-units-per-second))
