;;;; Constraint store for the CHR Scheme runtime.
;;;;
;;;; Manages constraint suspensions: creation, storage, killing, liveness
;;;; checking, field access, and snapshot-based iteration.  Integrates with
;;;; the observer/reactivation mechanism in (ychr var): when a constraint
;;;; is stored, it registers as an observer on its variable arguments so
;;;; that future unification triggers reactivation.
;;;;
;;;; Key design difference from the Haskell runtime: constraint identifiers
;;;; ARE suspension records (not integer keys into a lookup map), eliminating
;;;; an IntMap lookup on every store operation.

;;; --------------------------------------------------------------------------
;;; Growable vectors (internal)
;;; --------------------------------------------------------------------------

;; A growable vector: a mutable backing array with a fill count.
;; Amortized O(1) append via doubling.

(define-record-type <growable>
  (%make-growable storage count)
  growable?
  (storage growable-storage growable-storage-set!)
  (count growable-count growable-count-set!))

(define (make-growable capacity)
  (%make-growable (make-vector capacity #f) 0))

(define (growable-push! g value)
  (let ((n (growable-count g))
        (s (growable-storage g)))
    (when (= n (vector-length s))
      (let ((new-s (make-vector (* 2 (vector-length s)) #f)))
        (vector-copy! new-s 0 s)
        (growable-storage-set! g new-s)
        (set! s new-s)))
    (vector-set! s n value)
    (growable-count-set! g (+ n 1))))

;;; --------------------------------------------------------------------------
;;; Suspensions
;;; --------------------------------------------------------------------------

;; A constraint suspension.  The suspension record itself serves as the
;; constraint identifier — no separate ID-to-suspension map is needed.

(define-record-type <suspension>
  (%make-suspension id type args alive)
  suspension?
  (id suspension-id)                                ; fixnum, unique
  (type suspension-type)                            ; fixnum (constraint type index)
  (args suspension-args)                            ; vector of values
  (alive suspension-alive? suspension-alive-set!))  ; boolean, mutable

(define (suspension-arg susp idx)
  (vector-ref (suspension-args susp) idx))

;;; --------------------------------------------------------------------------
;;; Store state (module-level)
;;; --------------------------------------------------------------------------

;; by-type: vector of <growable>, indexed by constraint type.
;; next-id: counter for fresh suspension IDs.

(define *store-by-type* #f)
(define *store-next-id* 0)

(define (init-store! num-types)
  (set! *store-next-id* 0)
  (let ((v (make-vector num-types #f)))
    (let loop ((i 0))
      (when (< i num-types)
        (vector-set! v i (make-growable 16))
        (loop (+ i 1))))
    (set! *store-by-type* v)))

;;; --------------------------------------------------------------------------
;;; Operations
;;; --------------------------------------------------------------------------

;; Allocate a new suspension.  Alive but not yet in the type-indexed store.
;; Returns the suspension (which IS the constraint identifier).
(define (create-constraint ctype args)
  (let ((id *store-next-id*))
    (set! *store-next-id* (+ id 1))
    (%make-suspension id ctype args #t)))

;; Add a suspension to the type-indexed store and register it as an
;; observer on each of its variable arguments.
(define (store-constraint susp)
  (let ((g (vector-ref *store-by-type* (suspension-type susp)))
        (a (suspension-args susp))
        (sid (suspension-id susp)))
    (growable-push! g susp)
    ;; Register as observer on variable arguments
    (let ((len (vector-length a)))
      (let loop ((i 0))
        (when (< i len)
          (add-observer! sid (vector-ref a i))
          (loop (+ i 1)))))))

;; Kill a constraint (set alive to #f).
(define (kill-constraint susp)
  (suspension-alive-set! susp #f))

;; Check if a constraint is still alive.
(define (alive-constraint? susp)
  (suspension-alive? susp))

;; Get a constraint argument by 0-based index.
(define (constraint-arg susp idx)
  (vector-ref (suspension-args susp) idx))

;; Get the integer ID of a constraint (for propagation history).
(define (constraint-id susp)
  (suspension-id susp))

;; Get the constraint type index.
(define (constraint-type susp)
  (suspension-type susp))

;; Compare two constraint identifiers for equality.
(define (id-equal? s1 s2)
  (eq? s1 s2))

;; Check if a suspension has the given constraint type.
(define (is-constraint-type? susp ctype)
  (= (suspension-type susp) ctype))

;; Get a snapshot of all suspensions of a given type.
;; Returns a <snapshot>: the backing vector and the count at snapshot time.
;; New constraints appended after this call are not visible to the iterator.
(define (store-snapshot ctype)
  (let ((g (vector-ref *store-by-type* ctype)))
    (values (growable-storage g) (growable-count g))))

;; Accessors for snapshot iteration.
;; A snapshot is (values vector count) — use these after receiving the values.
(define (snapshot-length count) count)
(define (snapshot-ref storage i) (vector-ref storage i))
