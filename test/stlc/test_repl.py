"""End-to-end tests for the STLC example's surface parser + REPL.

Each case pipes one line of surface syntax into the ``stlc-typechecker``
binary (its default REPL mode) and checks that the rendered inference
result appears in stdout. This exercises the whole pipeline: parse ->
encode (ToTerm) -> typecheck (the CHR module, via runQueryCompiled) ->
decode (FromTerm) -> render.

To add a case, append a (source, expected_substring) tuple to REPL_CASES.
"""

import subprocess

import pytest

REPL_CASES = [
    ("\\x. x + 1", "int -> int"),
    ("\\x. x", "a -> a"),
    ("(\\x. x + 1) 5", "int"),
    ("\\x. \\y. x", "a -> b -> a"),
    ("\\f. \\x. f (f x)", "(a -> a) -> a -> a"),
    ("let f = \\x. x + 1 in f 5", "int"),
    # Self-application is ill-typed in STLC (no polymorphism).
    ("\\x. x x", "cannot construct the infinite type"),
    ("1 2", "cannot unify int with (int -> _)"),
    ("y", "unbound variable y"),
    # A syntax error is reported, not crashed on.
    ("\\x.", "parse error"),
]


@pytest.mark.parametrize(
    "source,expected", REPL_CASES, ids=[c[0] for c in REPL_CASES]
)
def test_stlc_repl(source, expected, stlc_bin):
    result = subprocess.run(
        [stlc_bin],
        input=source + "\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert expected in result.stdout, (
        f"expected {expected!r} in output for {source!r}:\n{result.stdout}"
    )


def test_stlc_demo(stlc_bin):
    """The --demo table runs and reports the polymorphic identity type."""
    result = subprocess.run(
        [stlc_bin, "--demo"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"demo failed:\n{result.stdout}\n{result.stderr}"
    assert "a -> a" in result.stdout
    assert "(a -> a) -> a -> a" in result.stdout
