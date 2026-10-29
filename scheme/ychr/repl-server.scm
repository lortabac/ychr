;;;; Chez Scheme server for the YCHR REPL's Scheme backend.
;;;;
;;;; The Haskell REPL writes one generated query expression to stdin and
;;;; reads one frame from stderr. User output and the query result go to
;;;; stdout, which the REPL inherits, so protocol traffic and user output
;;;; never interleave.
;;;;
;;;; The generated library is fixed to `(ychr generated repl)`, so its
;;;; session thunk is `repl`. The query code relies on the names below:
;;;; `%s`, `fresh-session`, `start-timer`, `report-timer` and, from
;;;; `(ychr pretty)`, `pretty-query-result`.
(import (rnrs)
        (rnrs eval)
        (ychr runtime)
        (ychr pretty)
        (ychr generated repl))

(define %s #f)

(define (fresh-session) (repl))

;; Process CPU time, in the same unit the Haskell REPL reports. The
;; result is formatted as seconds with six decimals.
(define (start-timer) (current-time 'time-process))

(define (time->ns t)
  (+ (* (time-second t) 1000000000) (time-nanosecond t)))

(define (report-timer start)
  (let* ((elapsed (- (time->ns (current-time 'time-process)) (time->ns start)))
         (elapsed (if (negative? elapsed) 0 elapsed))
         (us (div elapsed 1000))
         (secs (div us 1000000))
         (frac (mod us 1000000)))
    (display "Time: ")
    (display secs)
    (display ".")
    (let ((digits (number->string frac)))
      (display (make-string (- 6 (string-length digits)) #\0))
      (display digits))
    (display "s")
    (newline)))

(define (emit line)
  (display line (current-error-port))
  (newline (current-error-port))
  (flush-output-port (current-error-port)))

(define (escape-line s)
  (let-values (((port extract) (open-string-output-port)))
    (string-for-each
     (lambda (c)
       (cond
         ((char=? c #\\) (put-string port "\\\\"))
         ((char=? c #\newline) (put-string port "\\n"))
         ((char=? c #\return) (put-string port "\\r"))
         (else (put-char port c))))
     s)
    (extract)))

(define (condition-text c)
  (if (message-condition? c)
      (condition-message c)
      (let-values (((port extract) (open-string-output-port)))
        (display c port)
        (extract))))

(define (respond-ok)
  (emit "YCHR-REPL-OK"))

(define (respond-error c)
  (emit (string-append "YCHR-REPL-ERR " (escape-line (condition-text c)))))

(define (loop)
  ;; A read or decoding failure leaves the input port in an unknown state,
  ;; so report the error and exit rather than trying to resynchronize. The
  ;; REPL can restart the backend with :recompile.
  (let ((e (guard (c (#t (respond-error c) (eof-object)))
              (read (current-input-port)))))
    (unless (eof-object? e)
      (guard (c (#t
                 (flush-output-port (current-output-port))
                 (respond-error c)))
        (eval e (interaction-environment))
        (flush-output-port (current-output-port))
        (respond-ok))
      (loop))))

(emit "YCHR-REPL-READY")
(loop)
