;;;; Constraint store for the CHR Scheme runtime.
(library (ychr store)
  (export make-store-by-type
          create-constraint
          store-constraint
          kill-constraint
          alive-constraint?
          constraint-id
          constraint-arg
          constraint-type
          id-equal?
          is-constraint-type?
          store-snapshot
          snapshot-length
          snapshot-ref
          suspension?
          suspension-alive?
          suspension-arg
          suspension-id
          suspension-type)
  (import (rnrs)
          (ychr session)
          (ychr var))

  ;;; Growable vectors (internal)
  (define-record-type (growable %make-growable growable?)
    (fields (mutable storage growable-storage growable-storage-set!)
            (mutable count growable-count growable-count-set!)))

  (define (make-growable capacity)
    (%make-growable (make-vector capacity #f) 0))

  (define (vector-copy!/ychr to at from)
    (do ((i 0 (+ i 1)))
        ((= i (vector-length from)))
      (vector-set! to (+ at i) (vector-ref from i))))

  (define (growable-push! g value)
    (let ((n (growable-count g))
          (s (growable-storage g)))
      (when (= n (vector-length s))
        (let ((new-s (make-vector (* 2 (vector-length s)) #f)))
          (vector-copy!/ychr new-s 0 s)
          (growable-storage-set! g new-s)
          (set! s new-s)))
      (vector-set! s n value)
      (growable-count-set! g (+ n 1))))

  ;;; Suspensions
  (define-record-type (suspension %make-suspension suspension?)
    (fields (immutable id suspension-id)
            (immutable type suspension-type)
            (immutable args suspension-args)
            (mutable alive suspension-alive? suspension-alive-set!)))

  (define (suspension-arg susp idx)
    (vector-ref (suspension-args susp) idx))

  ;;; Initialize the by-type vector for a given number of constraint types.
  (define (make-store-by-type num-types)
    (let ((v (make-vector num-types #f)))
      (do ((i 0 (+ i 1))) ((= i num-types))
        (vector-set! v i (make-growable 16)))
      v))

  ;;; Operations
  (define (create-constraint s ctype args)
    (let ((id (session-store-next-id s)))
      (session-store-next-id-set! s (+ id 1))
      (%make-suspension id ctype args #t)))

  (define (store-constraint s susp)
    (let ((g (vector-ref (session-store-by-type s) (suspension-type susp)))
          (a (suspension-args susp)))
      (growable-push! g susp)
      (let ((len (vector-length a)))
        (let loop ((i 0))
          (when (< i len)
            (add-observer! susp (vector-ref a i))
            (loop (+ i 1)))))))

  (define (kill-constraint susp)
    (suspension-alive-set! susp #f))

  (define (alive-constraint? susp)
    (suspension-alive? susp))

  (define (constraint-arg susp idx)
    (vector-ref (suspension-args susp) idx))

  (define (constraint-id susp)
    (suspension-id susp))

  (define (constraint-type susp)
    (suspension-type susp))

  (define (id-equal? s1 s2)
    (eq? s1 s2))

  (define (is-constraint-type? susp ctype)
    (= (suspension-type susp) ctype))

  (define (store-snapshot s ctype)
    (let ((g (vector-ref (session-store-by-type s) ctype)))
      (values (growable-storage g) (growable-count g))))

  (define (snapshot-length count) count)
  (define (snapshot-ref storage i) (vector-ref storage i))
)
