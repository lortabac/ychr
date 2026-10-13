;;;; The search undo trail: recording writes, marking a position, and
;;;; unwinding back to one.
;;;;
;;;; Search backtracking on this backend is almost entirely trail. The
;;;; driver (`(ychr runtime)`) snapshots only the reactivation queue,
;;;; which is per session. Everything else a branch can write is shared
;;;; with the caller and recorded here write-by-write, then replayed in
;;;; reverse: logical-variable values and observer lists, the @alive@ /
;;;; @stored@ flags on suspensions, the growable counts, the store-index
;;;; pointer and every index entry filed while a search is active, and
;;;; the propagation history.
;;;;
;;;; The recording hooks sit at the choke points that own those cells —
;;;; `unify*`, `add-observer!` and `value-key` in @(ychr var)@, the flag
;;;; writes, the growable, `file-backlog!` and `file-entry!` in
;;;; @(ychr store)@, `add-history!` in @(ychr history)@ — so no caller
;;;; has to remember to trail anything.
;;;; When no search is active (`trail-active?` is @#f@) every hook is
;;;; one box read.
;;;;
;;;; The trail is global rather than per session, matching the Haskell
;;;; runtime's `SessionEnv.trail`: `deref`, `unify` and `kill-constraint`
;;;; are called with no session in hand, and a fork must share the
;;;; caller's trail so that a nested search's commit stays undoable by
;;;; the enclosing driver. It is installed by the outermost driver and
;;;; restored when that driver exits; a nested driver finds one active
;;;; and leaves it alone.
;;;;
;;;; Entries are undo thunks, newest first. `deref`'s path compression is
;;;; the one write that is *not* recorded: while a trail is active the
;;;; driver skips it instead (see @(ychr var)), which is cheaper than
;;;; trailing it and equally sound — a skipped compression only makes a
;;;; later walk longer, never changes the answer.
(library (ychr trail)
  (export trail-active?
          trail-push!
          trail-mark
          trail-unwind!
          trail-enter!
          trail-exit!
          trail-box)
  (import (rnrs))

  ;;; Slot 0: the current trail, or @#f@ when no search is active.
  ;;; Slot 1: its length, kept alongside so that `trail-mark` and
  ;;; `trail-unwind!` are O(1) to start. A mark is taken per alternative,
  ;;; and a search path of depth k has a trail of length O(k), so calling
  ;;; `length` there made a deep search quadratic. A vector so the hooks
  ;;; can read and write it without a session, and so `trail-enter!` /
  ;;; `trail-exit!` can save and restore it around a nested search.
  (define trail-box (vector #f 0))

  (define (trail-active?) (vector-ref trail-box 0))

  ;;; Record one undo thunk, immediately before the write it undoes.
  ;;; A no-op when no search is active. Callers guard on
  ;;; `trail-active?` where the old value is cheap to read anyway, and
  ;;; rely on this check where reading it is not free.
  (define (trail-push! thunk)
    (let ((entries (vector-ref trail-box 0)))
      (when entries
        (vector-set! trail-box 0 (cons thunk entries))
        (vector-set! trail-box 1 (+ (vector-ref trail-box 1) 1)))))

  ;;; The current trail position: the number of entries recorded so far,
  ;;; or 0 when no search is active — the honest answer, since there is
  ;;; then nothing recorded to undo.
  (define (trail-mark)
    (if (vector-ref trail-box 0) (vector-ref trail-box 1) 0))

  ;;; Undo every write recorded since @mark@, newest first, and drop
  ;;; those entries.
  ;;;
  ;;; Replaying an entry writes back a value the cell provably held at
  ;;; that point in the run, and entries are replayed in the exact
  ;;; reverse of the order they were made, so a cell written several
  ;;; times inside the branch ends up holding the value it had at the
  ;;; mark. A mark beyond the current length is "nothing to do" rather
  ;;; than an error: marks are taken by nested drivers in increasing
  ;;; order and unwound to in decreasing order, so it cannot arise.
  (define (trail-unwind! mark)
    (when (vector-ref trail-box 0)
      (let loop ()
        (when (> (vector-ref trail-box 1) mark)
          (let ((head (car (vector-ref trail-box 0))))
            (vector-set! trail-box 0 (cdr (vector-ref trail-box 0)))
            (vector-set! trail-box 1 (- (vector-ref trail-box 1) 1))
            (head)
            (loop))))))

  ;;; Install a fresh empty trail and return the previous box state, or
  ;;; return the current state unchanged when a trail is already active.
  ;;; The state is the entries and the length together, as a pair; the
  ;;; caller hands it to `trail-exit!` without looking inside.
  ;;;
  ;;; A nested search shares its parent's trail: variable cells are
  ;;; shared across forks even when the store is not, so an outer branch
  ;;; that fails must be able to undo a binding an inner search
  ;;; committed. Marks, not trails, are what delimit an undo.
  (define (trail-enter!)
    (let ((prev (cons (vector-ref trail-box 0) (vector-ref trail-box 1))))
      (unless (car prev)
        ;; A fresh trail is an empty entry list; what is returned is what
        ;; the caller restores on exit, whose entries are `#f` — no trail.
        ;; They are different values, and conflating them leaks an active
        ;; trail.
        (vector-set! trail-box 0 '())
        (vector-set! trail-box 1 0))
      prev))

  ;;; Restore what `trail-enter!` returned. Called once per driver exit,
  ;;; after the unwind, so the caller sees the trail state it had.
  (define (trail-exit! prev)
    (vector-set! trail-box 0 (car prev))
    (vector-set! trail-box 1 (cdr prev)))
)
