"""Terms survive Chez's fasl across processes.

The term record types are nongenerative (scheme/ychr/var.sls), so a
ground term written by one process reads back in another one as the
same record types, for typed functors (`m__f`) and bare ones (`f`). One process writes, a second one reads and checks.
Chez only: fasl is Chez-specific. Skipped when Chez is not installed.
"""

import os
import shutil
import subprocess

import pytest

TERMS = """
(define (args n)
  (let ((v (make-vector n)))
    (do ((i 0 (+ i 1))) ((= i n) v) (vector-set! v i (+ i 1)))))

(define (terms)
  (append
   (list (list 1 2 3)
         (make-term 'm__f (args 9))
         (make-term 'm__g
                    (vector (list 1 (make-term 'm__h (args 2)))
                            "s" 'a 1.5
                            (make-term 'm__k (args 10)))))
   (let loop ((n 8) (acc '()))
     (if (= n 0) acc (loop (- n 1) (cons (make-term 'm__f (args n)) acc))))
   ;; Bare functors: one shared type per arity, the functor in a field.
   (list (make-term 'f (args 1))
         (make-term 'f (args 2))
         (make-term 'g (vector (make-term 'h (args 3)) 'a))
         (make-term 'f (args 9)))))
"""

WRITER = """
(import (rnrs) (only (chezscheme) fasl-write) (ychr var))
""" + TERMS + """
(let ((p (open-file-output-port (cadr (command-line))
                                (file-options no-fail))))
  (fasl-write (terms) p)
  (close-port p))
"""

READER = """
(import (rnrs) (only (chezscheme) fasl-read) (ychr var))
""" + TERMS + """
(let* ((p (open-file-input-port (cadr (command-line))))
       (got (fasl-read p)))
  (close-port p)
  (unless (and (= (length got) (length (terms)))
               (for-all equal?/chr got (terms))
               (for-all term? got)
               (compound*? (list-ref got 1))
               (match-term (list-ref got 11) 'f 1)
               (match-term (list-ref got 12) 'f 2)
               (not (match-term (list-ref got 12) 'g 2))
               (match-term (list-ref got 14) 'f 9)
               (let loop ((i 3) (n 1))
                 (or (> n 8)
                     (let ((t (list-ref got i)))
                       (and (compound? t)
                            (= (term-arity t) n)
                            (match-term t 'm__f n)
                            (loop (+ i 1) (+ n 1)))))))
    (display "mismatch")
    (exit 1))
  (display "ok"))
"""


@pytest.fixture(scope="module")
def chez():
    command = os.environ.get("YCHR_SCHEME", "scheme")
    if shutil.which(command) is None:
        pytest.skip(f"no Chez Scheme executable found (tried {command})")
    return command


def run(chez, project_root, script, data):
    return subprocess.run(
        [
            chez,
            "--libdirs",
            os.path.join(project_root, "scheme"),
            "--libexts",
            ".sls",
            "--program",
            script,
            data,
        ],
        capture_output=True,
        text=True,
        timeout=120,
    )


def test_fasl_round_trip(chez, project_root, tmp_path):
    writer = tmp_path / "writer.sps"
    reader = tmp_path / "reader.sps"
    data = str(tmp_path / "terms.fasl")
    writer.write_text(WRITER)
    reader.write_text(READER)
    w = run(chez, project_root, str(writer), data)
    assert w.returncode == 0, w.stderr
    r = run(chez, project_root, str(reader), data)
    assert r.returncode == 0, r.stdout + r.stderr
    assert r.stdout == "ok"
