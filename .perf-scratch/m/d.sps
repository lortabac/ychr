(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((R (make-var %s)))
    (m:go/1 %s R)
    (pretty-bindings (list (cons (quote R) R)))
))
