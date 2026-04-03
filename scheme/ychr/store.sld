(define-library (ychr store)
  (export init-store!
          create-constraint
          store-constraint
          kill-constraint
          alive-constraint?
          constraint-id
          constraint-arg
          constraint-type
          id-equal?
          is-constraint-type?
          store-snapshot
          snapshot-length
          snapshot-ref
          suspension?
          suspension-alive?
          suspension-arg
          suspension-id
          suspension-type)
  (import (scheme base)
          (ychr var))
  (include "store.scm"))
