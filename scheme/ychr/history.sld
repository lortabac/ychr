(define-library (ychr history)
  (export init-history!
          add-history!
          not-in-history?)
  (import (scheme base)
          (srfi 69))
  (include "history.scm"))
