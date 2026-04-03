(import (rnrs)
        (srfi :64)
        (ychr runtime))

(test-begin "reactivation")

(test-group "empty-queue"
  (let ((s (%make-session 0))
        (called #f))
    (drain-queue! s (lambda (sid) (set! called #t)))
    (test-assert "callback not called" (not called))))

(test-group "enqueue-and-drain"
  (let ((s (%make-session 0)))
    (enqueue! s '(1 2 3))
    (let ((result '()))
      (drain-queue! s (lambda (sid) (set! result (cons sid result))))
      (test-equal "FIFO order" '(3 2 1) result))))

(test-group "multiple-enqueues"
  (let ((s (%make-session 0)))
    (enqueue! s '(10 20))
    (enqueue! s '(30))
    (let ((result '()))
      (drain-queue! s (lambda (sid) (set! result (cons sid result))))
      (test-equal "all in order" '(30 20 10) result))))

(test-group "drain-empty-after-drain"
  (let ((s (%make-session 0)))
    (enqueue! s '(1))
    (drain-queue! s (lambda (sid) #f))
    (let ((called #f))
      (drain-queue! s (lambda (sid) (set! called #t)))
      (test-assert "empty after drain" (not called)))))

(test-group "reentrant-enqueue"
  (let ((s (%make-session 0)))
    (enqueue! s '(1 2))
    (let ((result '()))
      (drain-queue! s
       (lambda (sid)
         (set! result (cons sid result))
         (when (= sid 1)
           (enqueue! s '(10 11)))))
      (test-equal "reentrant items picked up"
        '(11 10 2 1) result))))

(test-group "deeply-reentrant"
  (let ((s (%make-session 0)))
    (enqueue! s '(1))
    (let ((result '()))
      (drain-queue! s
       (lambda (sid)
         (set! result (cons sid result))
         (when (< sid 3)
           (enqueue! s (list (+ sid 1))))))
      (test-equal "chain of reentrant enqueues"
        '(3 2 1) result))))

(test-group "enqueue-empty-list"
  (let ((s (%make-session 0))
        (called #f))
    (enqueue! s '())
    (drain-queue! s (lambda (sid) (set! called #t)))
    (test-assert "empty enqueue is no-op" (not called))))

(test-end "reactivation")
