(import (rnrs)
        (srfi :64)
        (ychr runtime)
        (ychr store))

(test-begin "reactivation")

;;; The queue holds suspensions now, not raw ids: `enqueue!` drops a dead
;;; suspension and one belonging to another session's store, so it has to
;;; read the record. These helpers make suspensions that pass both tests.

(define (a-session n)
  (%make-session n))

(define (fresh-suspension s n)
  (create-constraint s 0 (vector n)))

(define (ids-of result)
  (map suspension-id result))

(test-group "empty-queue"
  (let ((s (a-session 1))
        (called #f))
    (drain-queue! s (lambda (sid) (set! called #t)))
    (test-assert "callback not called" (not called))))

(test-group "enqueue-and-drain"
  (let ((s (a-session 1)))
    (enqueue! s (map (lambda (n) (fresh-suspension s n)) '(0 1 2)))
    (let ((result '()))
      (drain-queue! s (lambda (sid) (set! result (cons sid result))))
      (test-equal "FIFO order" '(2 1 0) (ids-of result)))))

(test-group "multiple-enqueues"
  (let ((s (a-session 1)))
    (enqueue! s (map (lambda (n) (fresh-suspension s n)) '(0 1)))
    (enqueue! s (list (fresh-suspension s 2)))
    (let ((result '()))
      (drain-queue! s (lambda (sid) (set! result (cons sid result))))
      (test-equal "all in order" '(2 1 0) (ids-of result)))))

(test-group "drain-empty-after-drain"
  (let ((s (a-session 1)))
    (enqueue! s (list (fresh-suspension s 1)))
    (drain-queue! s (lambda (sid) #f))
    (let ((called #f))
      (drain-queue! s (lambda (sid) (set! called #t)))
      (test-assert "empty after drain" (not called)))))

(test-group "reentrant-enqueue"
  (let* ((s (a-session 1))
         (one (fresh-suspension s 1))
         (two (fresh-suspension s 2))
         (ten (fresh-suspension s 10))
         (eleven (fresh-suspension s 11)))
    (enqueue! s (list one two))
    (let ((result '()))
      (drain-queue! s
       (lambda (sid)
         (set! result (cons sid result))
         (when (= (suspension-id sid) 0)
           (enqueue! s (list ten eleven)))))
      (test-equal "reentrant items picked up"
        '(3 2 1 0) (ids-of result)))))

(test-group "deeply-reentrant"
  (let* ((s (a-session 1))
         (one (fresh-suspension s 1))
         (two (fresh-suspension s 2))
         (three (fresh-suspension s 3)))
    (enqueue! s (list one))
    (let ((result '()))
      (drain-queue! s
       (lambda (sid)
         (set! result (cons sid result))
         ;; Ids are 0, 1, 2 for the three suspensions; each turn queues the
         ;; next, so the drain reaches all three.
         (when (< (suspension-id sid) 2)
           (enqueue! s (list (if (= (suspension-id sid) 0) two three))))))
      (test-equal "chain of reentrant enqueues"
        '(2 1 0) (ids-of result)))))

(test-group "enqueue-empty-list"
  (let ((s (a-session 1))
        (called #f))
    (enqueue! s '())
    (drain-queue! s (lambda (sid) (set! called #t)))
    (test-assert "empty enqueue is no-op" (not called))))

;;; A killed suspension is dropped at enqueue time: its activation could
;;; only re-store it.
(test-group "dead-suspensions-are-dropped"
  (let* ((s (a-session 1))
         (dead (fresh-suspension s 1)))
    (kill-constraint dead)
    (enqueue! s (list dead))
    (let ((called #f))
      (drain-queue! s (lambda (sid) (set! called #t)))
      (test-assert "killed suspension not queued" (not called)))))

;;; A suspension belonging to another session's store is foreign: its id
;;; names nothing here, so activating it would be a cross-session leak.
(test-group "foreign-suspensions-are-dropped"
  (let* ((s (a-session 1))
         (other (a-session 1))
         (foreign (create-constraint other 0 (vector 1))))
    (enqueue! s (list foreign))
    (let ((called #f))
      (drain-queue! s (lambda (sid) (set! called #t)))
      (test-assert "foreign suspension not queued" (not called)))))

(test-end "reactivation")
