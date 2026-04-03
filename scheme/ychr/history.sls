;;;; Propagation history for the CHR Scheme runtime.
(library (ychr history)
  (export add-history!
          not-in-history?)
  (import (rnrs)
          (ychr session))

  (define (add-history! s rule-name ids)
    (hashtable-set! (session-history s) (cons rule-name ids) #t))

  (define (not-in-history? s rule-name ids)
    (not (hashtable-contains? (session-history s) (cons rule-name ids))))
)
