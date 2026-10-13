(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((Ss (make-var %s))
         (X (make-var %s)))
    (q:go/2 %s Ss X)
    (pretty-bindings (list (cons (quote Ss) Ss) (cons (quote X) X)))
))
