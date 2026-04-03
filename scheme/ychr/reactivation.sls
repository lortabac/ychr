;;;; Reactivation queue for the CHR Scheme runtime.
(library (ychr reactivation)
  (export enqueue!
          drain-queue!)
  (import (rnrs)
          (ychr session))

  (define (enqueue! s ids)
    (let loop ((ids ids))
      (when (pair? ids)
        (session-queue-back-set! s (cons (car ids) (session-queue-back s)))
        (loop (cdr ids)))))

  (define (dequeue! s)
    (if (pair? (session-queue-front s))
        (let ((val (car (session-queue-front s))))
          (session-queue-front-set! s (cdr (session-queue-front s)))
          val)
        (if (pair? (session-queue-back s))
            (begin
              (session-queue-front-set! s (reverse (session-queue-back s)))
              (session-queue-back-set! s '())
              (dequeue! s))
            #f)))

  (define (drain-queue! s callback)
    (let loop ()
      (let ((sid (dequeue! s)))
        (when sid
          (callback sid)
          (loop)))))
)
