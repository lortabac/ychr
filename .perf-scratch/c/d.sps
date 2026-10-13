(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((Ok (make-var %s))
         (X (make-var %s)))
    (c:go/2 %s Ok X)
    (pretty-bindings (list (cons (quote Ok) Ok) (cons (quote X) X)))
))
