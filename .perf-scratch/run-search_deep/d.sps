(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((X (make-var %s))
         (N (make-var %s)))
    (search_deep:deep_count/3 %s 200 X N)
    (pretty-bindings (list (cons (quote N) N) (cons (quote X) X)))
))
