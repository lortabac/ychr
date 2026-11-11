;;;; The interface `ychr scheme-types` generates for bench_expr.chr, over
;;;; one sealed native record type per constructor. The reference the
;;;; generated libraries are measured against (`build/native`, ...).
(library (bench expr-native)
  (export make-lit lit? lit-1 make-neg neg? neg-1
          make-add add? add-1 add-2 make-mul mul? mul-1 mul-2
          make-ifz ifz? ifz-1 ifz-2 ifz-3)
  (import (rnrs base) (rnrs records syntactic))
  (define-record-type (lit make-lit lit?) (sealed #t) (fields (immutable a lit-1)))
  (define-record-type (neg make-neg neg?) (sealed #t) (fields (immutable a neg-1)))
  (define-record-type (add make-add add?) (sealed #t)
    (fields (immutable a add-1) (immutable b add-2)))
  (define-record-type (mul make-mul mul?) (sealed #t)
    (fields (immutable a mul-1) (immutable b mul-2)))
  (define-record-type (ifz make-ifz ifz?) (sealed #t)
    (fields (immutable a ifz-1) (immutable b ifz-2) (immutable c ifz-3))))
