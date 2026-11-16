(import (rnrs)
        (srfi :64)
        (ychr runtime)
        (ychr trail))

;; Tests for the store's per-argument indexes (the paper's Indexing
;; optimization). See store.sls and src/YCHR/Internal/Runtime/Index.hs.
;;
;; The property under test throughout is the one the optimization rests
;; on: the index may narrow the iterator, but never below the matching
;; suspensions, and never out of store order.

(test-begin "index")

;; A session whose type 0 has argument position 0 looked up through an
;; index condition, the arrangement every candidate test below assumes.
(define (index-session)
  (%make-session 2 (list (cons 0 (list 0)))))

;; Store `susp` and return it, for convenience.
(define (tell! s susp)
  (store-constraint s susp)
  susp)

;; Store `n` ground suspensions of type 0 whose indexed argument is the
;; given value.
(define (tell-ground-n! s n arg)
  (do ((i 0 (+ i 1)))
      ((= i n))
    (store-constraint s (create-constraint s 0 (vector arg)))))

;; A lookup answer (five values, see store.sls) as a list, walked the
;; way the generated loop walks it: merge the two slot vectors.
(define (answer->list vec bs bn rs rn)
  (let loop ((i 0) (j 0) (acc '()))
    (let ((tb (and (< i bn)
                   (or (>= j rn) (< (vector-ref bs i) (vector-ref rs j))))))
      (if (or tb (< j rn))
          (let ((susp (vector-ref vec (cond ((not tb) (vector-ref rs j))
                                            (bs (vector-ref bs i))
                                            (else i)))))
            (if tb
                (loop (+ i 1) j (cons susp acc))
                (loop i (+ j 1) (cons susp acc))))
          (reverse acc)))))

;; The suspensions a lookup for `key` may return, as a list.
(define (candidates s ctype pos key)
  (call-with-values (lambda () (candidate-suspensions s ctype pos key))
    answer->list))

(define (candidate-count s ctype pos key)
  (let-values (((vec bs bn rs rn) (candidate-suspensions s ctype pos key)))
    (+ bn rn)))

;; ---------------------------------------------------------------------------
;; Keys
;; ---------------------------------------------------------------------------

(test-group "ground-key"
  (let ((s (%make-session 0)))
    (test-equal "integer" '(num . 1) (ground-key 1))
    (test-equal "float" '(num . 1.5) (ground-key 1.5))
    (test-equal "negative float" '(num . -1.5) (ground-key -1.5))
    (test-equal "atom" '(atom . a) (ground-key 'a))
    (test-equal "text" '(text . "s") (ground-key "s"))
    (test-equal "boolean" '(bool . #t) (ground-key #t))
    (test-equal "empty-ish zero" '(num . 0) (ground-key 0))
    ;; -0.0 and 0.0 collapse: `eqv?` distinguishes them, so the key is
    ;; coarser than ask-equality in the safe direction (extra candidates
    ;; only).
    (test-equal "negative zero normalizes" '(num . 0) (ground-key -0.0))
    (test-equal "zero equal" (ground-key 0.0) (ground-key -0.0))
    ;; Every NaN collapses, and a NaN key is stable.
    (test-equal "nan normalizes" '(num . nan) (ground-key +nan.0))
    (test-equal "nan equal" (ground-key +nan.0) (ground-key +nan.0))
    ;; `nan?` is not total on numbers — it raises on a non-real complex —
    ;; so the key walk must guard it. A store that used to scan has to
    ;; keep working once its type is indexed, and raising here would be
    ;; exactly the kind of behaviour change the index must never make.
    (test-equal "complex has a key, not a raise"
                (cons 'num (make-rectangular 1 2))
                (ground-key (make-rectangular 1 2)))
    ;; Exactness is preserved: `equal?/chr` never equates 1 with 1.0.
    (test-assert "exact vs inexact distinct"
                 (not (equal? (ground-key 1) (ground-key 1.0))))
    (test-equal "compound"
                '(term f (num . 1) (atom . a))
                (ground-key (make-term 'f (vector 1 'a))))
    (test-equal "nested compound"
                '(term f (term g (text . "x")))
                (ground-key (make-term 'f (vector (make-term 'g (vector "x"))))))
    ;; Not ground: an unbound variable, or a compound holding one.
    (let ((x (make-var s)))
      (test-assert "unbound var has no key" (not (ground-key x)))
      (test-assert "term holding an unbound var has no key"
                   (not (ground-key (make-term 'f (vector 1 x)))))
      (test-assert "nested unbound var has no key"
                   (not (ground-key (make-term 'f (vector (make-term 'g (vector x)))))))
      ;; A bound variable takes the key of its value.
      (%unify s x 7)
      (test-equal "bound var takes its value's key" '(num . 7) (ground-key x)))))

;; ---------------------------------------------------------------------------
;; Index state
;; ---------------------------------------------------------------------------

(test-group "indexed-positions-for"
  (test-group "no positions configured"
    (let ((s (%make-session 1)))
      (tell-ground-n! s (+ index-threshold 4) 0)
      (test-assert "never indexed" (not (indexed-positions-for s 0)))))
  (test-group "on demand"
    (let ((s (index-session)))
      (test-assert "unindexed before the threshold"
                   (not (indexed-positions-for s 0)))
      (tell-ground-n! s (- index-threshold 1) 0)
      (test-assert "still unindexed one store short"
                   (not (indexed-positions-for s 0)))
      (tell-ground-n! s 1 0)
      (test-equal "indexed from the crossing store" '(0)
                  (indexed-positions-for s 0)))
    (let ((s (index-session)))
      (tell-ground-n! s (+ index-threshold 1) 0)
      (test-equal "positions reported" '(0) (indexed-positions-for s 0)))))

;; ---------------------------------------------------------------------------
;; Candidate sets
;; ---------------------------------------------------------------------------

(test-group "candidate-suspensions"
  (test-group "unindexed type scans"
    (let* ((s (index-session))
           (a (tell! s (create-constraint s 0 (vector 1))))
           (b (tell! s (create-constraint s 0 (vector 2)))))
      (test-equal "whole bucket below the threshold" (list a b)
                  (candidates s 0 0 (ground-key 1)))))

  (test-group "crossing the threshold files the backlog"
    (let ((s (index-session)))
      ;; Fifteen ground stores, then a non-ground one: the non-ground
      ;; store is the one that crosses the threshold, so the whole
      ;; pre-threshold bucket is filed from it.
      (do ((i 0 (+ i 1)))
          ((= i (- index-threshold 1)))
        (store-constraint s (create-constraint s 0 (vector i))))
      (let* ((x (make-var s))
             (straddler (tell! s (create-constraint s 0 (vector x)))))
        (test-equal "indexed at the crossing store" '(0)
                    (indexed-positions-for s 0))
        ;; The straddler landed in the fallback set, so it answers a
        ;; lookup for any key...
        (test-equal "fallback reaches the non-ground store"
                    (list straddler)
                    (candidates s 0 0 (ground-key 100)))
        ;; ...and binding it afterwards does not move it out.
        (%unify s x 100)
        (test-equal "still reachable after binding"
                    (list straddler)
                    (candidates s 0 0 (ground-key 100)))
        ;; The backlog is filed: a ground key answers from its bucket
        ;; plus the fallback, in store order.
        (test-equal "bucket plus fallback, in store order" 2
                    (candidate-count s 0 0 (ground-key 3)))
        (let ((cs (candidates s 0 0 (ground-key 3))))
          (test-equal "bucket entry first" 3 (suspension-id (car cs)))
          (test-equal "fallback entry second" straddler (cadr cs))))))

  (test-group "all non-ground falls back to the snapshot"
    (let ((s (index-session)))
      (do ((i 0 (+ i 1)))
          ((= i (+ index-threshold 2)))
        (store-constraint s (create-constraint s 0 (vector (make-var s)))))
      (test-equal "every store is in the fallback set" (+ index-threshold 2)
                  (candidate-count s 0 0 (ground-key 1)))))

  (test-group "killed constraints stay candidates"
    (let ((s (index-session)))
      (do ((i 0 (+ i 1)))
          ((= i index-threshold))
        (store-constraint s (create-constraint s 0 (vector i))))
      (let ((victim (create-constraint s 0 (vector 5))))
        (store-constraint s victim)
        (kill-constraint victim)
        ;; The iterator's liveness check filters it, exactly as it does
        ;; for a scan; the index itself never trims.
        (test-equal "no index entry is removed" 2
                    (candidate-count s 0 0 (ground-key 5))))))

  (test-group "store-constraint is idempotent"
    (let* ((s (index-session))
           (susp (create-constraint s 0 (vector 1))))
      (do ((i 0 (+ i 1)))
          ((= i index-threshold))
        (store-constraint s (create-constraint s 0 (vector (+ 100 i)))))
      (tell! s susp)
      (tell! s susp)
      (test-equal "filed once" 1 (candidate-count s 0 0 (ground-key 1)))))

  (test-group "compound ground keys"
    (let ((s (index-session)))
      (do ((i 0 (+ i 1)))
          ((= i index-threshold))
        (store-constraint s (create-constraint s 0 (vector (make-term 'f (vector i))))))
      (let ((target (tell! s (create-constraint s 0 (vector (make-term 'f (vector 'x)))))))
        (test-equal "structural key matches"
                    (list target)
                    (candidates s 0 0 (ground-key (make-term 'f (vector 'x)))))))))

;; ---------------------------------------------------------------------------
;; The answer is not a copy
;; ---------------------------------------------------------------------------

(test-group "lookup answer"
  (test-group "bucket and fallback interleave in store order"
    (let ((s (index-session)))
      (tell-ground-n! s index-threshold 0)
      (let* ((a (tell! s (create-constraint s 0 (vector (make-var s)))))
             (b (tell! s (create-constraint s 0 (vector 1))))
             (c (tell! s (create-constraint s 0 (vector (make-var s)))))
             (d (tell! s (create-constraint s 0 (vector 1))))
             (e (tell! s (create-constraint s 0 (vector (make-var s))))))
        (test-equal "merged" (list a b c d e)
                    (candidates s 0 0 (ground-key 1))))))

  (test-group "later stores are not seen"
    (let ((s (index-session)))
      (tell-ground-n! s index-threshold 0)
      (let ((a (tell! s (create-constraint s 0 (vector 1))))
            (u (tell! s (create-constraint s 0 (vector (make-var s))))))
        (let-values (((vec bs bn rs rn) (candidate-suspensions s 0 0 (ground-key 1))))
          ;; Enough stores to grow both slot vectors past their capacity.
          (do ((i 0 (+ i 1))) ((= i 20))
            (store-constraint s (create-constraint s 0 (vector 1)))
            (store-constraint s (create-constraint s 0 (vector (make-var s)))))
          (test-equal "old answer unchanged" (list a u)
                      (answer->list vec bs bn rs rn))
          (test-equal "a new lookup sees them" 42
                      (candidate-count s 0 0 (ground-key 1)))))))

  (test-group "search undo restores the index"
    (let ((s (index-session)))
      (tell-ground-n! s index-threshold 0)
      (let* ((a (tell! s (create-constraint s 0 (vector 1))))
             (u (tell! s (create-constraint s 0 (vector (make-var s)))))
             (prev (trail-enter!))
             (mark (trail-mark)))
        ;; An existing key, a new key, and the fallback set.
        (store-constraint s (create-constraint s 0 (vector 1)))
        (store-constraint s (create-constraint s 0 (vector 2)))
        (store-constraint s (create-constraint s 0 (vector (make-var s))))
        (test-equal "inside the branch" 4 (candidate-count s 0 0 (ground-key 1)))
        (test-equal "new key inside the branch" 3
                    (candidate-count s 0 0 (ground-key 2)))
        (trail-unwind! mark)
        (trail-exit! prev)
        (test-equal "old key restored" (list a u) (candidates s 0 0 (ground-key 1)))
        (test-equal "new key gone" (list u) (candidates s 0 0 (ground-key 2))))))

  ;; A loop around a search holds an answer while the branch pushes,
  ;; is undone, and the next push reuses the same slots.
  (test-group "a held answer survives a search undo"
    (let ((s (index-session)))
      (tell-ground-n! s index-threshold 0)
      (let ((a (tell! s (create-constraint s 0 (vector 1))))
            (u (tell! s (create-constraint s 0 (vector (make-var s))))))
        (let-values (((vec bs bn rs rn) (candidate-suspensions s 0 0 (ground-key 1))))
          (let* ((prev (trail-enter!))
                 (mark (trail-mark)))
            (do ((i 0 (+ i 1))) ((= i 10))
              (store-constraint s (create-constraint s 0 (vector 1)))
              (store-constraint s (create-constraint s 0 (vector (make-var s)))))
            (trail-unwind! mark)
            (trail-exit! prev))
          (do ((i 0 (+ i 1))) ((= i 10))
            (store-constraint s (create-constraint s 0 (vector 1)))
            (store-constraint s (create-constraint s 0 (vector (make-var s)))))
          (test-equal "held answer unchanged" (list a u)
                      (answer->list vec bs bn rs rn))
          (test-equal "new lookup" 22 (candidate-count s 0 0 (ground-key 1))))))))

;; ---------------------------------------------------------------------------
;; Several probes
;; ---------------------------------------------------------------------------

;; A session whose type 0 indexes argument positions 0 and 1.
(define (two-key-session)
  (%make-session 1 (list (cons 0 (list 0 1)))))

(define (candidates-among s ctype probes)
  (call-with-values (lambda () (candidate-suspensions-among s ctype probes))
    answer->list))

(test-group "candidate-suspensions-among"
  (test-group "drives from the position with fewer candidates"
    (let* ((s (two-key-session))
           (m (tell! s (create-constraint s 0 (vector 'o 7))))
           (u (tell! s (create-constraint s 0 (vector 'o (make-var s))))))
      ;; Every fact shares the first key; only two can match the second.
      (do ((i 0 (+ i 1)))
          ((= i 30))
        (store-constraint s (create-constraint s 0 (vector 'o (+ 100 i)))))
      (let ((p0 (cons 0 (ground-key 'o)))
            (p1 (cons 1 (ground-key 7))))
        (test-equal "small one second" (list m u)
                    (candidates-among s 0 (list p0 p1)))
        (test-equal "small one first" (list m u)
                    (candidates-among s 0 (list p1 p0))))))

  (test-group "a #f key is skipped"
    (let* ((s (two-key-session))
           (m (tell! s (create-constraint s 0 (vector 'o 7)))))
      (do ((i 0 (+ i 1)))
          ((= i 30))
        (store-constraint s (create-constraint s 0 (vector 'o (+ 100 i)))))
      (test-equal "only the usable probe drives" (list m)
                  (candidates-among s 0 (list (cons 0 #f) (cons 1 (ground-key 7)))))
      (test-equal "no usable probe: whole bucket" 31
                  (length (candidates-among s 0 (list (cons 0 #f) (cons 1 #f)))))))

  (test-group "a tie keeps the earlier probe"
    (let ((s (two-key-session)))
      (do ((i 0 (+ i 1)))
          ((= i 32))
        (store-constraint s (create-constraint s 0 (vector i (mod i 2)))))
      (let ((evens (candidates-among s 0 (list (cons 1 (ground-key 0))
                                               (cons 1 (ground-key 1)))))
            (odds (candidates-among s 0 (list (cons 1 (ground-key 1))
                                              (cons 1 (ground-key 0))))))
        (test-equal "first probe: key 0" 0 (constraint-arg (car evens) 1))
        (test-equal "first probe: key 1" 1 (constraint-arg (car odds) 1))
        (test-equal "sizes" '(16 16) (list (length evens) (length odds)))))))

;; ---------------------------------------------------------------------------
;; Observers
;; ---------------------------------------------------------------------------

(test-group "indexed positions still observe"
  (let ((s (index-session)))
    ;; Past the threshold, the observer registration and the key are
    ;; built by one traversal; a nested unbound variable must still be
    ;; observed, or binding it later would not reactivate the store.
    (do ((i 0 (+ i 1)))
        ((= i (- index-threshold 1)))
      (store-constraint s (create-constraint s 0 (vector i))))
    (let* ((x (make-var s))
           (watched (tell! s (create-constraint s 0 (vector (make-term 'g (vector x))))))
           (seen '()))
      (%unify s x 9)
      (drain-queue! s (lambda (id) (set! seen (cons id seen))))
      (test-equal "reactivation enqueued" (list watched) seen))))

(test-end "index")
