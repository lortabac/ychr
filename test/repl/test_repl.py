"""REPL integration tests.

Each test pipes a query into ``ychr repl --quiet`` and checks stdout.
To add a new test, append a (query, expected_output) tuple to REPL_TESTS.
"""

import subprocess

import pytest

REPL_TESTS = [
    ("R is 1 + 1.", "R = 2.\n"),
    ("identity(1, R).", "R = 1.\n"),
    ("R is call_fun(fun(X) -> X end, 1).", "R = 1.\n"),
    ("R is call_fun(fun(X, _) -> X end, 1, _).", "R = 1.\n"),
    ("R is var(_).", "R = true.\n"),
    ("R is var(1).", "R = false.\n"),
    ("R is integer(1).", "R = true.\n"),
    ('R is integer("hello").', "R = false.\n"),
    ('R is ground("hello").', "R = true.\n"),
    ("R is ground(foo(1, _)).", "R = false.\n"),
    (
        'T is read_term_from_string("foo(X, Y)"), [X, Y] is term_variables(T), X = 1, Y = 2.',
        "T = foo(1, 2),\nX = 1,\nY = 2.\n",
    ),
    ("R is member(1, []).", "R = false.\n"),
    ("R is member(1, [1]).", "R = true.\n"),
    ("R is member(1, [1, 2]).", "R = true.\n"),
    ("R is member(1, [0, 1, 2]).", "R = true.\n"),
    ("R is member(1, [0, 2]).", "R = false.\n"),
    ("1 = 2.", "Error: unification failure: cannot unify 1 with 2\n"),
    (
        "[X, Y] = [1, 2, 3].",
        "Error: unification failure: cannot unify [1, 2] with [1, 2, 3]\n",
    ),
]


@pytest.mark.parametrize("query,expected", REPL_TESTS, ids=[t[0] for t in REPL_TESTS])
def test_repl(query, expected, ychr_bin):
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=query + "\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout == expected
