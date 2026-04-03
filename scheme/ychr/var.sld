(define-library (ychr var)
  (export make-var
          var?
          var-id
          deref
          unify
          equal?/chr
          make-term
          term?
          term-functor
          term-args
          match-term
          get-arg
          add-observer!
          get-var-id
          reset-var-counter!
          *wildcard*
          wildcard?)
  (import (scheme base))
  (include "var.scm"))
