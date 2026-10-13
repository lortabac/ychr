"""Apply the two verified fixes to the restored runtime.sls:
the string comparison in alt-type-of, and a correctly-parenthesised
try-alternatives whose let* body is the if (not just its then-branch)."""

import subprocess

WT = "/home/lorenzo/Development/ychr/.worktrees/search-scheme-2"
PATH = WT + "/scheme/ychr/runtime.sls"

text = open(PATH, encoding="utf-8").read()

# --- Fix 1: alt-type-of compares strings. ---------------------------------
old = """  (define (alt-type-of names)
    (let ((target (string->symbol "search__alt"))
          (n (vector-length names)))
      (let loop ((i 0))
        (cond ((>= i n) #f)
              ((eq? (vector-ref names i) target) i)
              (else (loop (+ i 1)))))))"""
new = """  (define (alt-type-of names)
    (let ((target "search__alt")
          (n (vector-length names)))
      (let loop ((i 0))
        (cond ((>= i n) #f)
              ;; The table holds the mangled name as a *string* — the
              ;; compiler emits a `(vector "…")` literal — so the compare
              ;; is `string=?`, not `eq?`.
              ((and (string? (vector-ref names i))
                    (string=? (vector-ref names i) target))
               i)
              (else (loop (+ i 1)))))))"""
assert text.count(old) == 1, text.count(old)
text = text.replace(old, new, 1)

# --- Fix 2: try-alternatives, with the let* body closing properly. --------
lines = text.split("\n")
start = next(i for i, l in enumerate(lines) if l.startswith("  ;;; Try each alternative of one choice point"))
end = next(i for i, l in enumerate(lines) if l.startswith("  ;;; A value with every bound variable"))

FN = r'''  ;;; Try each alternative of one choice point in list order, undoing the
  ;;; branch between attempts. Exhausting them fails the choice point,
  ;;; which fails whatever branch contains it.
  ;;;
  ;;; A branch that *fails* — `with-failures-caught` answers a pair whose
  ;;; car is `failed` — is undone and the next alternative tried. A branch
  ;;; that succeeds answers whatever the solution handler asked for, and
  ;;; a handler asking for the next solution answers `failed` (see
  ;;; `on-step`), which is what makes every enclosing alternative level
  ;;; undo and try its next one too.
  (define (try-alternatives s susp slot goals on-step)
    (cond
      ((null? goals) (cons 'failed 'exhausted))
      (else
       (let ((goal (car goals)))
         (let* ((mark (trail-mark))
                (queue (begin-queue s))
                (result
                 (with-failures-caught
                  (lambda ()
                    ;; Taking the choice consumes it: an alternative must
                    ;; not rediscover its own choice point and recurse
                    ;; forever. The kill is trailed like any other flag
                    ;; write, so the constraint is alive again if this
                    ;; alternative is abandoned.
                    (kill-constraint susp)
                    ;; Resolved here, inside the branch, and without the
                    ;; export check: a lifted disjunct is a
                    ;; module-internal constraint, so the check that
                    ;; guards a caller-supplied goal would reject exactly
                    ;; the goals the compiler generated.
                    (for-each
                     (lambda (g)
                       (tell-goal s (car g) (cadr g) (car (cddr g)) "alt"))
                     (goal-tells s 'any-declared "alt" goal))
                    ;; Past this choice, not from the front: this one is
                    ;; killed just above. Each alternative gets the same
                    ;; starting point, because the undo below puts the
                    ;; bucket back exactly as it was.
                    (search-from s (+ slot 1) on-step)))))
           (if (or (not (eq? (car result) 'ok))
                   (eq? (cdr result) 'failed))
               (begin
                 (use-queue! s queue)
                 (trail-unwind! mark)
                 (try-alternatives s susp slot (cdr goals) on-step))
               (cdr result))))))))
'''
lines[start:end] = FN.rstrip("\n").split("\n")
text = "\n".join(lines)
open(PATH, "w", encoding="utf-8").write(text)
print("applied both fixes")
