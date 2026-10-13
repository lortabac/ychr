(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((X (make-var %s))
         (Ss (make-var %s)))
    (search_alt:disj_goal/2 %s X Ss)
    (pretty-bindings (list (cons (quote Ss) Ss) (cons (quote X) X)))
))
