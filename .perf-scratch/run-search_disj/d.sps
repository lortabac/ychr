(import (rnrs) (ychr runtime) (ychr pretty)
        (ychr generated program))

(let ((%s (program)))
  (let* ((V (make-var %s))
         (Ok (make-var %s)))
    (search_disj:undone/2 %s V Ok)
    (pretty-bindings (list (cons (quote Ok) Ok) (cons (quote V) V)))
))
