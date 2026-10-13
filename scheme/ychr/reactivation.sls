;;;; Reactivation queue for the CHR Scheme runtime.
(library (ychr reactivation)
  (export enqueue!
          drain-queue!)
  (import (rnrs)
          (ychr session)
          (ychr store))

  ;;; Append the suspensions a unification's observers point at to this
  ;;; session's queue, dropping the ones that could not activate
  ;;; anything.
  ;;;
  ;;; Two filters, both of them this backend's counterparts of the
  ;;; Haskell runtime's:
  ;;
  ;;;   * A dead suspension is queued no more. A killed constraint stays
  ;;;     on every observer list of the variables its arguments reach, so
  ;;;     a deep search would otherwise enqueue one dead choice point per
  ;;;;     level at every binding. The drain re-checks liveness anyway
  ;;;     (`alive-constraint?`), so this is a queue-traffic saving rather
  ;;;     than a correctness fix.
  ;;;   * A suspension owned by another session's store is dropped. A
  ;;;     constraint told inside a `run_chr_session` fork is owned by that
  ;;;     fork's store, never by the caller's, so if one of its ids is
  ;;;     ever enqueued in the caller the owner test answers "foreign"
  ;;;     and nothing is activated. This is the Scheme counterpart of the
  ;;;     Haskell runtime's `IntMap.lookup n storeById` — a cross-session
  ;;;     id hits an unknown suspension there and a foreign owner here.
  ;;;     A constraint of the caller's *is* owned by the caller's store,
  ;;;     so a forking search (`solve/1`, which shares the caller's store
  ;;;     objects) reactivates it inside the fork, which is what
  ;;;     `test/golden/search_fork/reactivated_in_fork` pins.
  ;;;
  ;;;   * A dead suspension is queued no more. A killed constraint stays
  ;;;     on every observer list of the variables its arguments reach, so
  ;;;     a deep search would otherwise enqueue one dead choice point per
  ;;;     level at every binding. The drain re-checks liveness anyway
  ;;;     (`alive-constraint?`), so this is a queue-traffic saving rather
  ;;;     than a correctness fix.
  ;;;   * A suspension owned by another session's store is dropped. A
  ;;;     constraint told inside a `run_chr_session` fork is owned by that
  ;;;     fork's store, never by the caller's, so if one of its ids is
  ;;;     ever enqueued in the caller the owner test answers "foreign"
  ;;;     and nothing is activated. This is the Scheme counterpart of the
  ;;;     Haskell runtime's `IntMap.lookup n storeById` — a cross-session
  ;;;     id hits an unknown suspension there and a foreign owner here.
  ;;;     A constraint of the caller's *is* owned by the caller's store,
  ;;;     so a forking search (`solve/1`, which shares the caller's store
  ;;;     objects) reactivates it inside the fork, which is what
  ;;;     `test/golden/search_fork/reactivated_in_fork` pins.
  ;;;
  ;;; The owner is read once for the whole batch rather than per id.
  (define (enqueue! s ids)
    (let ((owner (session-owner s)))
      (let loop ((ids ids))
        (when (pair? ids)
          (let ((susp (car ids)))
            (when (and (suspension-alive? susp)
                       (eq? (suspension-owner susp) owner))
              (session-queue-back-set! s
                                       (cons susp (session-queue-back s)))))
          (loop (cdr ids))))))

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
