;;;; Unified runtime for generated CHR programs.
(library (ychr runtime)
  (export
    ;; Session
    make-session session?
    ;; From (ychr var)
    make-var var? var-id deref unify equal?/chr
    make-term term? term-functor term-args
    match-term get-arg add-observer! get-var-id
    *wildcard* wildcard?
    ;; From (ychr store)
    make-store-by-type create-constraint store-constraint
    kill-constraint alive-constraint?
    constraint-id constraint-arg constraint-type
    id-equal? is-constraint-type?
    store-snapshot snapshot-length snapshot-ref
    suspension? suspension-alive? suspension-arg
    suspension-id suspension-type
    ;; From (ychr history)
    add-history! not-in-history?
    ;; From (ychr reactivation)
    enqueue! drain-queue!
    ;; Helpers for generated code
    %unify %nonvar? %chr-error %print %ground?
    %term-variables %compound-to-list %list-to-compound
    %read-term-from-string
    %nil %cons
    ;; Session initialization
    %make-session)
  (import (rnrs)
          (ychr session)
          (ychr var)
          (ychr store)
          (ychr history)
          (ychr reactivation))

  ;;; Session initialization: creates a fully initialized session
  (define (%make-session num-types)
    (make-session 0
                  (make-store-by-type num-types)
                  0
                  (make-hashtable equal-hash equal?)
                  '()
                  '()))

  ;;; Unify wrapper: unifies and enqueues observers
  (define (%unify s v1 v2)
    (let-values (((ok observers) (unify v1 v2)))
      (enqueue! s observers)
      ok))

  ;;; Type predicates
  (define (%nonvar? v) (not (var? v)))

  ;;; Error
  (define (%chr-error . args) (apply error "CHR runtime error" args))

  ;;; Print
  (define (%print v) (display v) (newline))

  ;;; Groundness check
  (define (%ground? v)
    (let ((d (deref v)))
      (cond ((var? d) #f)
            ((term? d)
             (let ((a (term-args d)))
               (let loop ((i 0))
                 (if (>= i (vector-length a)) #t
                     (and (%ground? (vector-ref a i))
                          (loop (+ i 1)))))))
            (else #t))))

  ;;; Prolog-style list helpers
  (define (%nil) (string->symbol "[]"))
  (define (%cons h t) (make-term (string->symbol ".") (vector h t)))
  (define (%nil? v) (and (symbol? v) (eq? v (string->symbol "[]"))))
  (define (%cons? v)
    (and (term? v)
         (eq? (term-functor v) (string->symbol "."))
         (= (vector-length (term-args v)) 2)))

  ;;; term_variables
  (define (%term-variables t)
    (let ((seen '()) (result '()))
      (define (walk v)
        (let ((d (deref v)))
          (cond ((var? d)
                 (let ((id (var-id d)))
                   (unless (memv id seen)
                     (set! seen (cons id seen))
                     (set! result (cons d result)))))
                ((term? d)
                 (let ((a (term-args d)))
                   (do ((i 0 (+ i 1))) ((= i (vector-length a)))
                     (walk (vector-ref a i))))))))
      (walk t)
      (fold-right %cons (%nil) (reverse result))))

  ;;; compound_to_list
  (define (%compound-to-list c)
    (let ((f (term-functor c)) (a (term-args c)))
      (let loop ((i (- (vector-length a) 1)) (acc (%nil)))
        (if (< i 0) (%cons f acc)
            (loop (- i 1) (%cons (vector-ref a i) acc))))))

  ;;; list_to_compound
  (define (%list-to-compound lst)
    (let loop ((l lst) (acc '()))
      (if (%cons? l)
          (loop (get-arg l 1) (cons (get-arg l 0) acc))
          (let ((parts (reverse acc)))
            (make-term (car parts) (list->vector (cdr parts)))))))

  ;;; read_term_from_string: stub
  (define (%read-term-from-string s)
    (error "%read-term-from-string" "not implemented"))
)
