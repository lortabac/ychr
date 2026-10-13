;;;; Propagation history for the CHR Scheme runtime.
(library (ychr history)
  (export add-history!
          not-in-history?)
  (import (rnrs)
          (ychr session)
          (ychr trail))

  ;;; The history is a shared hashtable across a forking search, so a
  ;;; branch's record has to come off when the branch is undone. A key
  ;;; is only ever added, never removed, while a branch runs — the
  ;;; `not-in-history?` test in front of every fire means a rule cannot
  ;;; record a key that is already there — so undoing the write by
  ;;; deleting the key restores the caller's history exactly.
  (define (add-history! s rule-name ids)
    (let ((key (cons rule-name ids)))
      (when (trail-active?)
        (trail-push! (lambda () (hashtable-delete! (session-history s) key))))
      (hashtable-set! (session-history s) key #t)))

  (define (not-in-history? s rule-name ids)
    (not (hashtable-contains? (session-history s) (cons rule-name ids))))
)
