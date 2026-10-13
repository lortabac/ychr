(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((Ok (make-var %s)))
    (search_basic:unify_ok/1 %s Ok)
    (pretty-bindings (list (cons (quote Ok) Ok)))
))
