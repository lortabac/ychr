(define-library (ychr reactivation)
  (export init-react-queue!
          enqueue!
          drain-queue!)
  (import (scheme base))
  (include "reactivation.scm"))
