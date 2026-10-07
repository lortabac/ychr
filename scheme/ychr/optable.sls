;;;; Operator tables for the CHR surface syntax.
;;;;
;;;; Both the term reader (@(ychr read)) and the pretty-printer
;;;; (@(ychr pretty)) need to know which names are operators and with
;;;; what fixity. The runtime also hands a table to `%read-term-from-string`
;;;; through the session. This library owns the representation so the
;;;; three agree.
;;;;
;;;; A table is `#(INFIX PREFIX WORD)`:
;;;;
;;;;   * INFIX and PREFIX are lists of `(name fixity type)` pairs, keyed
;;;;     by name string so no Scheme symbol escaping is needed for `|`,
;;;;     `;` or `\`; INFIX holds the infix and postfix operators, PREFIX
;;;;     the prefix ones — the split `YCHR.Internal.PExpr.OpTable` makes
;;;;     between `infixByName` and `prefixByName`;
;;;;   * WORD lists the non-symbolic operator names (`wordOpSet`).
;;;;
;;;; `builtin-op-entries` is a direct transcription of
;;;; `YCHR.Internal.Parser.builtinOps` in `(fixity type name)` form, the
;;;; shape `YCHR.Internal.PExpr.opTableEntries` returns; `make-op-table`
;;;; rebuilds a table from that shape. The generated library emits the
;;;; program's merged table (built-ins plus every operator the loaded
;;;; modules declare or import) as a `make-op-table` call over precisely
;;;; this entry list, so the reader can spell every operator the program
;;;; can.
(library (ychr optable)
  (export make-op-table builtin-op-entries builtin-op-table
          op-table-infix op-table-prefix op-table-word
          op-lookup max-prec max-arg-prec symbol-chars)
  (import (rnrs))

  ;; Precedence bounds of `YCHR.Internal.PExpr`: the maximum fixity an
  ;; operator may have, and the maximum one allowed inside a compound's
  ;; argument list (`,` sits at 1000, above this, so it separates
  ;; arguments).
  (define max-prec 1200)
  (define max-arg-prec 999)

  ;; Symbol characters of `YCHR.Internal.PExpr.symbolChars`.
  (define symbol-chars "\\:=<>+-*/#@^~!&?")

  (define (char-in-string? c str)
    (let loop ((i 0))
      (cond ((>= i (string-length str)) #f)
            ((char=? c (string-ref str i)) #t)
            (else (loop (+ i 1))))))

  ;; `YCHR.Internal.PExpr.isSymbolic`: every character is a symbol
  ;; character. `Data.Text.all` is true of the empty text, and the loop
  ;; below mirrors that.
  (define (symbolic-name? name)
    (let ((n (string-length name)))
      (let loop ((i 0))
        (or (>= i n)
            (and (char-in-string? (string-ref name i) symbol-chars)
                 (loop (+ i 1)))))))

  ;; Rebuild a table from `(fixity type name)` entries. The type decides
  ;; the list (prefix for `fx`/`fy`, infix/postfix for the rest) and the
  ;; name decides the word set. The order within a list is the entry
  ;; order; only the lookups are ever consulted, so it is unobservable.
  (define (make-op-table entries)
    (let loop ((es entries) (infix '()) (prefix '()) (word '()))
      (if (null? es)
          (vector (reverse infix) (reverse prefix) (reverse word))
          (let* ((e (car es))
                 (fix (car e))
                 (ty (cadr e))
                 (name (caddr e))
                 (prefix? (memq ty '(fx fy))))
            (loop (cdr es)
                  (if prefix? infix (cons (list name fix ty) infix))
                  (if prefix? (cons (list name fix ty) prefix) prefix)
                  (if (symbolic-name? name) word (cons name word)))))))

  (define (op-table-infix ops) (vector-ref ops 0))
  (define (op-table-prefix ops) (vector-ref ops 1))
  (define (op-table-word ops) (vector-ref ops 2))

  ;; The `(fixity type)` of an operator in a `(name fixity type)` list,
  ;; or #f. The first match is *the* match: within one category a name
  ;; has at most one entry — the built-in and arithmetic lists contain no
  ;; duplicates, and a generated table comes from the compiler's
  ;; conflict-checked `mergeOps`, whose `IntMap.unionWith nub` (the
  ;; `mkOpTable` shape) drops identical repeats — which is also why a
  ;; `Map.fromList` in the reference cannot disagree with this.
  (define (op-lookup name table)
    (cond ((null? table) #f)
          ((string=? name (car (car table))) (cdr (car table)))
          (else (op-lookup name (cdr table)))))

  ;; Every operator of `YCHR.Internal.Parser.builtinOps`. `end` is at
  ;; `max-prec + 1` so the Pratt parser never consumes it while its
  ;; presence in the word set keeps it out of `atomP`.
  (define builtin-op-entries
    '((100 yfx ":")
      (400 yfx "/")
      (500 fx "fun")
      (750 xfx "is")
      (750 xfx "=")
      (1000 xfy ",")
      (1105 xfy "|")
      (1110 xfy "->")
      (1100 xfy ";")
      (1100 xfx "\\")
      (1140 xfx "requiring")
      (1140 xfx "refining")
      (1150 xfx "--->")
      (1180 xfx "<=>")
      (1180 xfx "==>")
      (1180 fx "chr_constraint")
      (1180 fx "chr_type")
      (1180 fx "opaque_type")
      (1180 fx "function")
      (1180 fx "open_function")
      (1180 fx "class")
      (1180 fx "open_class")
      (1180 fx "extend_class_type")
      (1180 fx "extend_class")
      (1180 fx "extend_function")
      (1190 xfx "@")
      (1200 fx ":-")
      (1201 fx "end")))

  ;; The table a session with no compiled program gets — the Scheme
  ;; counterpart of `initSessionEnv`'s `builtinOps` default.
  (define builtin-op-table (make-op-table builtin-op-entries))
)
