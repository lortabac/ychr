(import (scheme base)
        (srfi 64)
        (ychr reactivation))

(test-begin "reactivation")

(test-group "empty-queue"
  (init-react-queue!)
  (let ((called #f))
    (drain-queue! (lambda (sid) (set! called #t)))
    (test-assert "callback not called" (not called))))

(test-group "enqueue-and-drain"
  (init-react-queue!)
  (enqueue! '(1 2 3))
  (let ((result '()))
    (drain-queue! (lambda (sid) (set! result (cons sid result))))
    (test-equal "FIFO order" '(3 2 1) result)))

(test-group "multiple-enqueues"
  (init-react-queue!)
  (enqueue! '(10 20))
  (enqueue! '(30))
  (let ((result '()))
    (drain-queue! (lambda (sid) (set! result (cons sid result))))
    (test-equal "all in order" '(30 20 10) result)))

(test-group "drain-empty-after-drain"
  (init-react-queue!)
  (enqueue! '(1))
  (drain-queue! (lambda (sid) #f))
  ;; Queue should now be empty
  (let ((called #f))
    (drain-queue! (lambda (sid) (set! called #t)))
    (test-assert "empty after drain" (not called))))

(test-group "reentrant-enqueue"
  (init-react-queue!)
  (enqueue! '(1 2))
  (let ((result '()))
    (drain-queue!
     (lambda (sid)
       (set! result (cons sid result))
       ;; When processing 1, enqueue 10 and 11
       (when (= sid 1)
         (enqueue! '(10 11)))))
    ;; Should process: 1, 2, 10, 11
    (test-equal "reentrant items picked up"
      '(11 10 2 1) result)))

(test-group "deeply-reentrant"
  (init-react-queue!)
  (enqueue! '(1))
  (let ((result '()))
    (drain-queue!
     (lambda (sid)
       (set! result (cons sid result))
       (when (< sid 3)
         (enqueue! (list (+ sid 1))))))
    ;; 1 -> enqueues 2 -> enqueues 3 -> stops
    (test-equal "chain of reentrant enqueues"
      '(3 2 1) result)))

(test-group "enqueue-empty-list"
  (init-react-queue!)
  (enqueue! '())
  (let ((called #f))
    (drain-queue! (lambda (sid) (set! called #t)))
    (test-assert "empty enqueue is no-op" (not called))))

(test-end "reactivation")
