;;;; Reactivation queue for the CHR Scheme runtime.
;;;;
;;;; Accumulates constraint suspension IDs that need reactivation
;;;; (typically enqueued as a side effect of unification) and provides
;;;; a drain operation that processes them one at a time.  The drain
;;;; re-reads the queue on every iteration so that IDs enqueued by
;;;; reentrant unifications during the callback are picked up.
;;;;
;;;; Implemented as a pair of lists (front/back) for amortized O(1)
;;;; enqueue and dequeue.

(define *queue-front* '())
(define *queue-back* '())

(define (init-react-queue!)
  (set! *queue-front* '())
  (set! *queue-back* '()))

;; Append suspension IDs to the back of the queue.
(define (enqueue! ids)
  (let loop ((ids ids))
    (when (pair? ids)
      (set! *queue-back* (cons (car ids) *queue-back*))
      (loop (cdr ids)))))

;; Dequeue one element.  Returns the element or #f if empty.
(define (dequeue!)
  (if (pair? *queue-front*)
      (let ((val (car *queue-front*)))
        (set! *queue-front* (cdr *queue-front*))
        val)
      (if (pair? *queue-back*)
          (begin
            (set! *queue-front* (reverse *queue-back*))
            (set! *queue-back* '())
            (dequeue!))
          #f)))

;; Drain the queue one element at a time, calling callback for each.
;; Re-reads the queue on every iteration so that IDs enqueued by the
;; callback (via reentrant unifications) are picked up.
(define (drain-queue! callback)
  (let loop ()
    (let ((sid (dequeue!)))
      (when sid
        (callback sid)
        (loop)))))
