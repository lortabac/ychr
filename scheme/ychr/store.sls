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
          suspension-alive-set!
          suspension-arg
          suspension-args
          suspension-id
          suspension-owner
          suspension-stored?
          suspension-stored-set!
          suspension-type
          ;; Store index (the paper's Indexing optimization) — see below.
          index-threshold
          make-index-positions
          make-store-index
          indexed-positions-for
          candidate-suspensions)
  (import (rnrs)
          (ychr session)
          (ychr var)
          (ychr trail))

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

  (define (growable-push! s g value)
    (trail-growable! g)
    (let ((n (growable-count g))
          (storage (growable-storage g)))
      (when (= n (vector-length storage))
        (let ((new-s (make-vector (* 2 (vector-length storage)) #f)))
          (vector-copy!/ychr new-s 0 storage)
          (growable-storage-set! g new-s)
          (set! storage new-s)))
      (vector-set! storage n value)
      (growable-count-set! g (+ n 1))))

  ;;; Suspensions. The stored flag makes store-constraint idempotent:
  ;;; under Late Storage the compiled code may reach a Store for the
  ;;; same suspension more than once (per fired kept occurrence, and at
  ;;; the end of every activation), and only the first may append to
  ;;; the store and register observers.
  ;;;
  ;;; `owner` is the identity token of the store the suspension belongs
  ;;; to (see `(ychr session)`). A session that tells a goal in a fresh
  ;;; sub-session creates suspensions owned by *that* store; if one of
  ;;; their ids is ever enqueued for reactivation in the session that
  ;;; called it, the owner test drops it rather than activating an
  ;;; unrelated constraint that happens to hold the same id.
  (define-record-type (suspension %make-suspension suspension?)
    (fields (immutable id suspension-id)
            (immutable type suspension-type)
            (immutable args suspension-args)
            (mutable alive suspension-alive? suspension-alive-set!)
            (mutable stored suspension-stored? suspension-stored-set!)
            (immutable owner suspension-owner)))

  (define (suspension-arg susp idx)
    (vector-ref (suspension-args susp) idx))

  ;;; Initialize the by-type vector for a given number of constraint types.
  (define (make-store-by-type num-types)
    (let ((v (make-vector num-types #f)))
      (do ((i 0 (+ i 1))) ((= i num-types))
        (vector-set! v i (make-growable 16)))
      v))

  ;;; -------------------------------------------------------------------
  ;;; Store index
  ;;;
  ;;; A per-(constraint type, argument position) index over the store:
  ;;; a bucket of store slots per ground key, plus the slots whose value
  ;;; at that position was not fully ground when it was stored. This is
  ;;; the Scheme counterpart of YCHR.Internal.Runtime.Index (the paper's
  ;;; Indexing optimization, §5.3); see that module for the reasoning.
  ;;;
  ;;; The index may only narrow the iterator, never lose a candidate:
  ;;; the per-candidate condition check in the generated code stays the
  ;;; decision procedure, so a candidate set is allowed to be a
  ;;; superset of the matches, never a subset. Two properties make that
  ;;; safe. A slot is filed under a key only when its value at the
  ;;; indexed position was fully ground when it was stored — ground
  ;;; values are immutable in this runtime, so the key cannot move under
  ;;; it — and every other slot goes to the position's non-ground
  ;;; fallback set, which every lookup for that position scans. And key
  ;;; equality is never finer than ask-equality (`equal?/chr`), which
  ;;; `value-key` in var.sls defends.
  ;;;
  ;;; Slots, not suspensions: the index stores positions in the type's
  ;;; growable vector, which is what makes ascending slot order
  ;;; reproduce the store's iteration order exactly. Slots stay valid
  ;;; because the store is only ever appended to, and its storage vector
  ;;; only ever grows by copying its prefix. There is no search driver
  ;;; on this backend, so unlike the Haskell runtime the index needs no
  ;;; snapshot or undo counterpart; a future one must capture and
  ;;; restore it together with the store.
  ;;; -------------------------------------------------------------------

  ;;; How many constraints of one type the store must hold before an
  ;;; index for it is worth maintaining. The trade is per store, not per
  ;;; lookup: filing an entry allocates a path through the index whether
  ;;; or not anything ever looks it up, while a bucket of a handful of
  ;;; constraints is cheaper to scan than to query. Mirrors
  ;;; `indexThreshold` in src/YCHR/Internal/Runtime/Index.hs; it is also
  ;;; tied to the fifteen padding stores in
  ;;; test/golden/index_ground_fallback, so keep the two in step.
  (define index-threshold 16)

  ;;; What is known about one argument position of one constraint type.
  ;;; Both slot lists are kept in descending order, because insertions
  ;;; arrive in ascending slot order and `cons` is the only cheap
  ;;; append; a lookup reverses the merge, which restores store order.
  (define-record-type (pos-index %make-pos-index pos-index?)
    (fields (immutable buckets pos-index-buckets)
            (mutable rest pos-index-rest pos-index-rest-set!)))

  (define (make-pos-index)
    (%make-pos-index (make-hashtable equal-hash equal?) '()))

  ;;; The index of one type: an alist from argument position to
  ;;; `pos-index`, holding exactly the positions the program looks up.
  (define (make-type-index positions)
    (map (lambda (pos) (cons pos (make-pos-index))) positions))

  ;;; The session's index-position vector: the positions a `Foreach`
  ;;; looks up per constraint type, `'()` for a type no condition names.
  ;;; `alist` is what the compiler emitted, one `(cons TYPE (list POS
  ;;; ...))` per indexed type.
  (define (make-index-positions num-types alist)
    (let ((v (make-vector num-types '())))
      (for-each
       (lambda (entry) (vector-set! v (car entry) (cdr entry)))
       alist)
      v))

  ;;; The session's store-index vector: `#f` per type until its bucket
  ;;; crosses `index-threshold`, then that type's alist index.
  (define (make-store-index num-types)
    (make-vector num-types #f))

  ;;; The positions a lookup can be answered from right now, or `#f`
  ;;; when the store has no index for the type — no position of it is
  ;;; ever looked up, or its bucket has not yet reached
  ;;; `index-threshold`. A caller that gets `#f` scans, and skips
  ;;; computing a lookup key it would not use. Mirrors
  ;;; `indexedPositionsFor` in src/YCHR/Internal/Runtime/Store.hs.
  (define (indexed-positions-for s ctype)
    (let ((positions (vector-ref (session-index-positions s) ctype)))
      (if (and (pair? positions)
               (vector-ref (session-store-index s) ctype))
          positions
          #f)))

  ;;; File one stored slot. A `#f` key means the argument was not fully
  ;;; ground when it was stored, so the slot goes to the position's
  ;;; fallback set and stays there: binding the variable afterwards does
  ;;; not re-file it.
  (define (file-entry! ti slot pos key)
    (let* ((pi (cdr (assv pos ti)))
           (buckets (pos-index-buckets pi)))
      (if key
          (hashtable-set! buckets key (cons slot (hashtable-ref buckets key '())))
          (pos-index-rest-set! pi (cons slot (pos-index-rest pi))))))

  ;;; A type that is being indexed from now on must still hold the
  ;;; suspensions stored below the threshold, which were never filed.
  ;;; Their observers were registered when they were stored, so only
  ;;; their keys are wanted here.
  ;;;
  ;;; The index this installs is new, so a search branch that indexes a
  ;;; type leaves nothing behind but the pointer: the driver records the
  ;;; old slot and puts it back, discarding every entry filed into the
  ;;; new structure. That is also why `file-entry!` needs no undo hook of
  ;;; its own — the only slot it can be handed came from here or from a
  ;;; type the branch itself pushed past `index-threshold`.
  (define (file-backlog! s ctype g positions)
    (let* ((ti (make-type-index positions))
           (storage (growable-storage g))
           (count (growable-count g)))
      (trail-store-index! s)
      (install-type-index! s ctype ti)
      (let loop ((slot 0))
        (when (< slot count)
          (let ((susp (vector-ref storage slot)))
            (for-each
             (lambda (pos)
               (file-entry! ti slot pos (ground-key (suspension-arg susp pos))))
             positions))
          (loop (+ slot 1))))))

  ;;; File the entries of one store: its slot plus one `(pos . key)` per
  ;;; indexed position, with a `#f` key for a non-ground argument.
  (define (insert-entries! s ctype slot entries)
    (let ((ti (vector-ref (session-store-index s) ctype)))
      (for-each
       (lambda (entry)
         (file-entry! ti slot (car entry) (cdr entry)))
       entries)))

  ;;; Register `susp` as an observer on every unbound variable reachable
  ;;; from its arguments — the pre-index traversal, unchanged.
  (define (observe-args! susp args)
    (let ((n (vector-length args)))
      (let loop ((i 0))
        (when (< i n)
          (add-observer! susp (vector-ref args i))
          (loop (+ i 1))))))

  ;;; One traversal per argument: register observers, and at an indexed
  ;;; position also build the argument's ground key. Returns the
  ;;; `(pos . key)` entries for the indexed positions.
  (define (keys-and-observe! susp positions)
    (let* ((args (suspension-args susp))
           (n (vector-length args)))
      (let loop ((i 0) (entries '()))
        (if (= i n)
            (reverse entries)
            (loop (+ i 1)
                  (if (memv i positions)
                      (cons (cons i (add-observer-and-key susp (vector-ref args i)))
                            entries)
                      (begin
                        (add-observer! susp (vector-ref args i))
                        entries)))))))

  ;;; Merge two descending, disjoint slot lists into one ascending list.
  ;;;
  ;;; Tail-recursive on purpose: the merge steps once per candidate and a
  ;;; bucket can be large, so a non-tail recursion would put the whole
  ;;; merged length on the stack where the scan this replaces used a flat
  ;;; loop. Taking the larger head first and consing builds the ascending
  ;;; prefix directly; whatever is left when one side runs out is
  ;;; descending and holds only smaller slots, so its reverse is
  ;;; prepended in one step.
  (define (merge-ascending a b)
    (let loop ((a a) (b b) (acc '()))
      (cond ((null? a) (append (reverse b) acc))
            ((null? b) (append (reverse a) acc))
            ((> (car a) (car b)) (loop (cdr a) b (cons (car a) acc)))
            (else (loop a (cdr b) (cons (car b) acc))))))

  ;;; The stored suspensions of a type that may hold an argument at
  ;;; `pos` `equal?/chr` to a value whose ground key is `key`, in store
  ;;; order. This is the lookup half of the optimization: where
  ;;; `store-snapshot` hands back the whole type bucket, this hands back
  ;;; the bucket's key plus the position's non-ground fallback set — a
  ;;; superset of the matches, which the caller's per-candidate check
  ;;; then narrows.
  ;;;
  ;;; A type the store is not indexing is answered by the whole bucket,
  ;;; which is the pre-index behaviour exactly. So is a candidate set
  ;;; that is not smaller than the bucket: the index has to prune to be
  ;;; worth the per-candidate bookkeeping it adds.
  (define (candidate-suspensions s ctype pos key)
    (let* ((g (vector-ref (session-store-by-type s) ctype))
           (storage (growable-storage g))
           (count (growable-count g))
           (ti (vector-ref (session-store-index s) ctype))
           (entry (and ti (assv pos ti)))
           (pi (and entry (cdr entry))))
      (if (not pi)
          (values storage count)
          (let* ((bucket (hashtable-ref (pos-index-buckets pi) key '()))
                 (slots (merge-ascending bucket (pos-index-rest pi)))
                 (n (length slots)))
            (if (>= n count)
                (values storage count)
                (let ((v (make-vector n)))
                  (let loop ((i 0) (ss slots))
                    (if (pair? ss)
                        (begin
                          (vector-set! v i (vector-ref storage (car ss)))
                          (loop (+ i 1) (cdr ss)))
                        (values v n)))))))))

  ;;; -------------------------------------------------------------------
  ;;; Search undo hooks
  ;;;
  ;;; The store is a shared object across a forking search: a `'copy`
  ;;; fork *is* the caller's store, so the driver undoes a branch's
  ;;; writes instead of discarding a private copy. Three of the writes
  ;;; need recording — the suspension `alive` and `stored` flags, and the
  ;;; growable's count — and all three are recorded only while a search
  ;;; is active.
  ;;;
  ;;; The growable's count is enough by itself: the store is append-only,
  ;;; so restoring an older count truncates exactly the suspensions a
  ;;; branch appended. Its storage vector only ever grows, and a vector
  ;;; swap copies the prefix, so a slot index a driver is holding names
  ;;; the same suspension before and after.
  ;;;
  ;;; The store index needs one more hook. An index is per type and lives
  ;;; in the session's `store-index` vector, which a fork shares; when a
  ;;; branch pushes a type past `index-threshold` it installs a whole new
  ;;; index there. Restoring the pointer discards that index, and
  ;;; `file-entry!` writes go only into an index the branch itself
  ;;; installed (see `file-backlog!`), so no per-entry hook is needed.
  ;;; -------------------------------------------------------------------

  (define (trail-growable! g)
    (when (trail-active?)
      (let ((old (growable-count g)))
        (trail-push! (lambda () (growable-count-set! g old))))))

  ;;; The whole index *pointer* is what a branch installs, so that is
  ;;; what is saved and restored: a fresh vector with the slot filled.
  ;;; The old vector object is untouched, so the entries filed into the
  ;;; new one disappear with it.
  (define (trail-store-index! s)
    (when (trail-active?)
      (let ((old (session-store-index s)))
        (trail-push!
         (lambda () (session-store-index-set! s old))))))

  ;;; Install a new store-index vector with `ctype`'s slot set to `ti`.
  (define (install-type-index! s ctype ti)
    (let* ((old (session-store-index s))
           (n (vector-length old))
           (new (make-vector n #f)))
      (do ((i 0 (+ i 1))) ((= i n))
        (vector-set! new i (vector-ref old i)))
      (session-store-index-set! s (if (< ctype n)
                                      (begin (vector-set! new ctype ti) new)
                                      new))))

  ;;; Operations
  (define (create-constraint s ctype args)
    (let ((id (session-store-next-id s)))
      (session-store-next-id-set! s (+ id 1))
      (%make-suspension id ctype args #t #f (session-owner s))))

  ;;; Add a constraint to the type-indexed store, register it as an
  ;;; observer on each of its variable arguments, and record it in the
  ;;; per-argument indexes the program's `Foreach` conditions can be
  ;;; answered from. Idempotent: the `stored` flag makes a repeated
  ;;; store a no-op, so a suspension cannot be appended twice, observed
  ;;; twice, or filed in the index twice.
  ;;;
  ;;; The index entries are the Indexing optimization; the argument walk
  ;;; that registers observers is the same one that computes an indexed
  ;;; argument's ground key (`keys-and-observe!`), so a store pays one
  ;;; traversal per argument, not two — and only once the type's bucket
  ;;; is worth indexing at all. Below `index-threshold` this is the
  ;;; pre-index path exactly.
  ;;;
  ;;; An *inert* type takes the plainest path of all: pushed, and
  ;;; nothing else. Nothing an inert constraint does can reactivate
  ;;; anything, so the walk that would register observers is skipped
  ;;; outright (Delay Avoidance's trivial instance). That is not only a
  ;;; saving: it is what makes `solve/1` accept a goal variable a
  ;;; caller's rule-less constraint mentions
  ;;; (`test/golden/search_fork/inert_watcher_ok`), and what keeps a deep
  ;;; search's choice points off every variable's observer list.
  (define (store-constraint s susp)
    ;; Only the *first* store records `stored` and puts anything in the
    ;; store. A re-store of an already-stored suspension is a no-op
    ;; (Late Storage emits one at the end of every activation), so
    ;; recording a trail entry here would let a search exit clear the
    ;; flag on a suspension that is still in the store — which would
    ;; both defeat `check-unwatched` and let the next re-store append
    ;; the same constraint twice.
    (unless (suspension-stored? susp)
      (when (trail-active?)
        (trail-push!
         (lambda () (suspension-stored-set! susp #f))))
      (suspension-stored-set! susp #t)
      (let* ((ctype (suspension-type susp))
             (g (vector-ref (session-store-by-type s) ctype))
             (positions (vector-ref (session-index-positions s) ctype)))
        (if (or (vector-ref (session-inert s) ctype) (null? positions))
            ;; Inert, or no position of this type is ever looked up
            ;; through an index: the pre-index path exactly. An inert
            ;; type registers no observers at all — that is what makes a
            ;; rule-less choice point free at every later binding, and
            ;; what keeps `check-unwatched` from seeing a live `alt` on
            ;; a goal variable.
            (begin
              (unless (vector-ref (session-inert s) ctype)
                (observe-args! susp (suspension-args susp)))
              (growable-push! s g susp))
            (let* ((slot (growable-count g))
                   (indexed (vector-ref (session-store-index s) ctype))
                   ;; `slot` is where this store lands, so the bucket
                   ;; holds `slot + 1` constraints once it has.
                   (worth (or indexed (>= (+ slot 1) index-threshold))))
              (if (not worth)
                  ;; Too small to be worth indexing: still the pre-index
                  ;; path, and the whole bucket is filed in one pass
                  ;; later if it grows past the threshold.
                  (growable-push! s g susp)
                  (let ((entries (keys-and-observe! susp positions)))
                    (when (not indexed)
                      (file-backlog! s ctype g positions))
                    (growable-push! s g susp)
                    (insert-entries! s ctype slot entries))))))))

  (define (kill-constraint susp)
    ;; Only `alive` is written, matching the reference: `stored` means
    ;; "has been stored", and `check-unwatched` reads the pair so that a
    ;; dead suspension's observer list stops counting. Clearing
    ;; `stored` here as well would make a kill-then-store re-append a
    ;; suspension that is already in the bucket.
    (when (trail-active?)
      (trail-push! (lambda () (suspension-alive-set! susp #t))))
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
