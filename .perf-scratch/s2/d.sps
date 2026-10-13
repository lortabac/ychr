(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((Ok (make-var %s))
         (Z (make-var %s)))
    (s2:go/2 %s Ok Z)
    (pretty-bindings (list (cons (quote Ok) Ok) (cons (quote Z) Z)))
))
