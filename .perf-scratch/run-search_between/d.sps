(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((X (make-var %s)))
    (search_between:outside_inverted/1 %s X)
    (pretty-bindings (list (cons (quote X) X)))
))
