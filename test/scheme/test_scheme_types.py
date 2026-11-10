"""Round trips for the library `ychr scheme-types` generates.

The fixture module (scheme_types/rt.chr) is compiled to Scheme, and its
types to a separate library. Scheme code builds values with the
generated constructors, passes them through CHR rules and reads them
back with the generated accessors. Runs on Guile, and on Chez when it is
installed; on Chez the values also go through fasl across processes.
"""

import os
import shutil
import subprocess

import pytest

FIXTURE = os.path.join(os.path.dirname(__file__), "scheme_types", "rt.chr")

ROUND_TRIP = """
(import (rnrs) (ychr runtime) (ychr generated rt) (ychr types rt))
(define s (rt))
(define (check name ok)
  (unless ok (display "FAIL ") (display name) (newline) (exit 1)))
(define (ask proc . args)
  (let ((r (make-var s)))
    (apply proc s (append args (list r)))
    (deref r)))

;; Values built in Scheme are matched by rule heads.
(check "circle" (eqv? 1 (ask rt:which/2 (make-circle 1.5))))
(check "rect" (eqv? 2 (ask rt:which/2 (make-rect 1.0 2.0))))
(check "empty" (eqv? 3 (ask rt:which/2 empty)))
(check "big" (eqv? 9 (ask rt:which/2 (make-big 1 2 3 4 5 6 7 8 9))))

;; A term from CHR whose fields were bound after it was built.
(let ((p (make-var s)))
  (rt:mk/1 s p)
  (check "point?" (point? p))
  (check "shape? is false" (not (shape? p)))
  (check "x" (eqv? 3 (point-x p)))
  (check "y is shallow" (pair? (point-y p)))
  (check "y deep" (equal? '(4) (deep-deref (point-y p)))))

;; Accessors agree with get_field, updates with set_field.
(let ((p (make-point 7 8)))
  (check "get_field" (equal?/chr (point-x p) (ask rt:getx/2 p)))
  (check "set_field" (equal?/chr (point-with-x p 9) (ask rt:setx/3 p 9)))
  (check "get_field y" (equal?/chr (point-y p) (ask rt:gety/2 p)))
  (check "set_field y" (equal?/chr (point-with-y p 1) (ask rt:sety/3 p 1)))
  (check "update keeps y" (eqv? 8 (point-y (point-with-x p 9)))))
(let ((c (make-circle 2.5)))
  (check "get_field r" (equal?/chr (circle-r c) (ask rt:getr/2 c))))

;; Predicates and positional accessors.
(check "rect-2" (eqv? 2.0 (rect-2 (make-rect 1.0 2.0))))
(check "big-9" (eqv? 9 (big-9 (make-big 1 2 3 4 5 6 7 8 9))))
(check "empty?" (empty? empty))
(check "shape?" (and (shape? empty) (shape? (make-rect 1.0 2.0))
                     (not (shape? (make-point 1 2)))))
(display "ok")
"""

CHECKED = """
(import (rnrs) (ychr var) (ychr types rt))
(display (guard (e ((assertion-violation? e) (condition-who e)))
  (point-x (make-circle 1.0))))
"""

ALONE = """
(import (rnrs) (ychr var) (ychr types rt))
(let ((p (make-point 1 (make-circle 2.0))))
  (if (and (point? p) (circle? (point-y p)) (eqv? 2.0 (circle-r (point-y p))))
      (display "ok")
      (display "FAIL")))
"""

FASL_WRITE = """
(import (rnrs) (only (chezscheme) fasl-write) (ychr types rt))
(let ((port (open-file-output-port (cadr (command-line)) (file-options no-fail))))
  (fasl-write (list (make-point 1 (make-big 1 2 3 4 5 6 7 8 9)) empty
                    (make-rect 1.0 2.0))
              port)
  (close-port port))
"""

FASL_READ = """
(import (rnrs) (only (chezscheme) fasl-read) (ychr types rt))
(let* ((port (open-file-input-port (cadr (command-line))))
       (vs (fasl-read port)))
  (close-port port)
  (let ((p (car vs)))
    (if (and (point? p) (eqv? 1 (point-x p)) (big? (point-y p))
             (eqv? 9 (big-9 (point-y p)))
             (empty? (cadr vs)) (rect? (caddr vs))
             (eqv? 2.0 (rect-2 (caddr vs))))
        (display "ok")
        (display "FAIL"))))
"""


@pytest.fixture(scope="module")
def libs(ychr_bin, project_root, tmp_path_factory):
    """Compile the fixture program and its types library once."""
    out = tmp_path_factory.mktemp("scheme_types")
    program = out / "program"
    types = out / "types"
    for args in (
        ["compile", "-t", "scheme", "-n", "rt", "-d", str(program), FIXTURE],
        ["scheme-types", "-d", str(types), FIXTURE],
    ):
        r = subprocess.run(
            [ychr_bin, args[0], "--Werror", *args[1:]],
            capture_output=True,
            text=True,
            cwd=project_root,
        )
        assert r.returncode == 0, r.stdout + r.stderr
    return {"program": str(program), "types": str(types)}


def run_guile(guile_bin, dirs, script, tmp_path, *args):
    path = tmp_path / "script.sps"
    path.write_text(script)
    cmd = [guile_bin, "--r6rs", "--no-auto-compile", "-x", ".sls"]
    for d in dirs:
        cmd += ["-L", d]
    return subprocess.run(
        cmd + [str(path), *args], capture_output=True, text=True, timeout=300
    )


def chez_command():
    command = os.environ.get("YCHR_SCHEME", "scheme")
    if shutil.which(command) is None:
        pytest.skip(f"no Chez Scheme executable found (tried {command})")
    return command


def run_chez(dirs, script, tmp_path, name, *args):
    path = tmp_path / name
    path.write_text(script)
    return subprocess.run(
        [chez_command(), "--libdirs", ":".join(dirs), "--libexts", ".sls",
         "--program", str(path), *args],
        capture_output=True,
        text=True,
        timeout=300,
    )


def test_round_trip_guile(guile_bin, libs, project_root, tmp_path):
    dirs = [os.path.join(project_root, "scheme"), libs["program"], libs["types"]]
    r = run_guile(guile_bin, dirs, ROUND_TRIP, tmp_path)
    assert r.returncode == 0 and r.stdout == "ok", r.stdout + r.stderr


def test_loads_alone_guile(guile_bin, libs, project_root, tmp_path):
    # No compiled program on the library path.
    dirs = [os.path.join(project_root, "scheme"), libs["types"]]
    r = run_guile(guile_bin, dirs, ALONE, tmp_path)
    assert r.returncode == 0 and r.stdout == "ok", r.stdout + r.stderr


def test_checked_accessor_raises(guile_bin, ychr_bin, project_root, tmp_path):
    out = tmp_path / "checked"
    r = subprocess.run(
        [ychr_bin, "scheme-types", "--checked", "-d", str(out), FIXTURE],
        capture_output=True, text=True, cwd=project_root,
    )
    assert r.returncode == 0, r.stdout + r.stderr
    dirs = [os.path.join(project_root, "scheme"), str(out)]
    r = run_guile(guile_bin, dirs, CHECKED, tmp_path)
    assert r.returncode == 0 and r.stdout == "point-x", r.stdout + r.stderr


def test_round_trip_chez(libs, project_root, tmp_path):
    dirs = [os.path.join(project_root, "scheme"), libs["program"], libs["types"]]
    r = run_chez(dirs, ROUND_TRIP, tmp_path, "rt.sps")
    assert r.returncode == 0 and r.stdout == "ok", r.stdout + r.stderr


def test_loads_alone_chez(libs, project_root, tmp_path):
    dirs = [os.path.join(project_root, "scheme"), libs["types"]]
    r = run_chez(dirs, ALONE, tmp_path, "alone.sps")
    assert r.returncode == 0 and r.stdout == "ok", r.stdout + r.stderr


def test_fasl_generated_accessors_chez(libs, project_root, tmp_path):
    dirs = [os.path.join(project_root, "scheme"), libs["types"]]
    data = str(tmp_path / "values.fasl")
    w = run_chez(dirs, FASL_WRITE, tmp_path, "w.sps", data)
    assert w.returncode == 0, w.stderr
    r = run_chez(dirs, FASL_READ, tmp_path, "r.sps", data)
    assert r.returncode == 0 and r.stdout == "ok", r.stdout + r.stderr
