"""Rewrite on-step and try-alternatives with a single, unambiguous
contract: the solution handler returns either a real value or the symbol
'failed meaning "request the next solution"."""

WT = "/home/lorenzo/Development/ychr/.worktrees/search-scheme-2"
PATH = WT + "/scheme/ychr/runtime.sls"

text = open(PATH, encoding="utf-8").read()

ON_STEP_OLD_START = "      (define (on-step step)"
ON_STEP_OLD_END = "      (define (body)"


def replace_block(text, start_marker, end_marker, body):
    i = text.index(start_marker)
    j = text.index(end_marker, i)
    return text[:i] + body + text[j:]


ON_STEP = r'''      (define (on-step step)
        (if (not (eq? step 'solution))
            'failed
            ;; `on-solution` answers a real value, or the symbol `failed`
            ;; when the handler asked for the next solution. An ambiguous
            ;; pair is not used: a handler's value can itself be a pair.
            (let ((decision (on-solution)))
              (cond
                ((eq? decision 'continue) 'failed)
                ((eq? decision 'stop)
                 (set! outcome 'stopped)
                 'stopped)
                ((eq? decision 'commit)
                 ;; Read before the unwind below takes the solution away.
                 (set! kept (map resolve-value goal-vars))
                 (set! outcome 'committed)
                 'committed)
                (else
                 (%chr-error
                  (string-append
                   "fold_solutions: the step function must return continue/1,"
                   " stop/1 or commit/1")))))))
'''
text = replace_block(text, ON_STEP_OLD_START, ON_STEP_OLD_END, ON_STEP)

TRY_OLD_START = "  ;;; Try each alternative of one choice point in list order"
TRY_OLD_END = "  ;;; A value with every bound variable"

TRY = r'''  ;;; Try each alternative of one choice point in list order, undoing the
  ;;; branch between attempts.
  ;;;
  ;;; Contract: this answers either the value the solution handler
  ;;; returned, or the symbol `failed`. `with-failures-caught` already
  ;;; turns an abandoned branch into `failed`, so the single check below
  ;;; covers both "the branch failed" and "the handler asked for the next
  ;;; solution" — which is what makes every enclosing alternative level
  ;;; undo and try its next one too.
  (define (try-alternatives s susp slot goals on-step)
    (if (null? goals)
        'failed
        (let* ((goal (car goals))
               (mark (trail-mark))
               (queue (begin-queue s))
               (branch
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
                   (search-from s (+ slot 1) on-step))))
               (value (if (pair? branch)
                          (if (eq? (car branch) 'ok) (cdr branch) 'failed)
                          'failed)))
          (if (eq? value 'failed)
              (begin
                (use-queue! s queue)
                (trail-unwind! mark)
                (try-alternatives s susp slot (cdr goals) on-step))
              value))))

'''
text = replace_block(text, TRY_OLD_START, TRY_OLD_END, TRY)

# The search driver's own failure path must match the new contract.
old = """      (define (body)
        (for-each
         (lambda (g)
           (tell-goal sub (car g) (cadr g) (car (cddr g)) "solve"))
         goals)
        (search-from sub cursor on-step))"""
new = """      (define (body)
        (for-each
         (lambda (g)
           (tell-goal sub (car g) (cadr g) (car (cddr g)) "solve"))
         goals)
        (search-from sub cursor on-step))"""
assert text.count(old) == 1
open(PATH, "w", encoding="utf-8").write(text)
print("rewrote on-step and try-alternatives")
