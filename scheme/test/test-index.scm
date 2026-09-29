(import (rnrs)
        (srfi :64)
        (ychr runtime))

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

;; The suspensions a lookup for `key` may return, as a list.
(define (candidates s ctype pos key)
  (let-values (((vec count) (candidate-suspensions s ctype pos key)))
    (let loop ((i 0) (acc '()))
      (if (= i count)
          (reverse acc)
          (loop (+ i 1) (cons (snapshot-ref vec i) acc))))))

(define (candidate-count s ctype pos key)
  (let-values (((vec count) (candidate-suspensions s ctype pos key)))
    count))

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
