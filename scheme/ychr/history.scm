;;;; Propagation history for the CHR Scheme runtime.
;;;;
;;;; Tracks which rule has fired with which combination of constraint
;;;; identifiers, to prevent redundant re-firing of propagation rules.
;;;; Uses an SRFI-69 hash table with equal?-based keys.
;;;; Keys are lists (rule-name id1 id2 ...) where rule-name is a symbol
;;;; and ids are fixnums (suspension-id values from (ychr store)).

(define *history* #f)

(define (init-history!)
  (set! *history* (make-hash-table equal?)))

;; Record that a rule has fired with the given constraint identifiers.
(define (add-history! rule-name ids)
  (hash-table-set! *history* (cons rule-name ids) #t))

;; Check that a rule has NOT fired with the given constraint identifiers.
;; Returns #t if the entry is absent (i.e. the rule may fire).
(define (not-in-history? rule-name ids)
  (not (hash-table-exists? *history* (cons rule-name ids))))
