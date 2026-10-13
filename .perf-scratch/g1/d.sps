(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((X (make-var %s))
         (M (make-var %s)))
    (search_basic:prop_rollback/2 %s X M)
    (pretty-bindings (list (cons (quote M) M) (cons (quote X) X)))
))
