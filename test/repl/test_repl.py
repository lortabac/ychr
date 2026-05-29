"""REPL integration tests.

Each test pipes a query into ``ychr repl --quiet`` and checks stdout.
To add a new test, append a (query, expected_output) tuple to REPL_TESTS.
"""

import subprocess

import pytest

REPL_TESTS = [
    ("R is 1 + 1.", "R = 2.\n"),
    ("R is '$call'(fun(X) -> X end, 1).", "R = 1.\n"),
    ("R is '$call'(fun(X) -> X + 1 end, 1).", "R = 2.\n"),
    ("R is '$call'(fun(X, _) -> X end, 1, _).", "R = 1.\n"),
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
    ("R is compound_to_list(term(1 + 1)).", "R = ['+', 1, 1].\n"),
    ("R is copy_term(term(foo(X))), X = 1.", "R = foo(_),\nX = 1.\n"),
    # Synthetic qualified atoms (no real module `foo`) require the
    # `term/1` opt-out: the renamer treats `term(X)` as fully opaque
    # data, so no module-visibility check fires on the qualified
    # `:`-compound inside.
    ("host:print(term(':'(foo, bar))).", "foo:bar\n"),
    ("host:print(1 + 1).", "2\n"),
    ("print(1 + 1).", "2\n"),
    ("'$call'(fun(X) -> host:print(X) end, 1 + 1).", "2\n"),
    ("host:print((foo, bar)).", "foo, bar\n"),
    ("host:print((foo; bar)).", "foo; bar\n"),
    ("host:print(','(foo, bar)).", "foo, bar\n"),
    ("host:print(';'(foo, bar)).", "foo; bar\n"),
    ("host:print((foo,(bar;baz))).", "foo, (bar; baz)\n"),
    ("host:print((foo,(bar,baz))).", "foo, bar, baz\n"),
    # Boolean output is bare `true`/`false` regardless of the path that
    # produced it: `is`-RHS literal (evalNestedExpr), `=` operand
    # (termToValue), comparison host call, and the explicit qualified
    # form `prelude:true()`. The cross-form case at the end confirms
    # that `=`-bound and comparison-produced booleans share a single
    # runtime representation (otherwise `==` would fail).
    ("B is true.", "B = true.\n"),
    ("B is false.", "B = false.\n"),
    ("X = true.", "X = true.\n"),
    ("X = false.", "X = false.\n"),
    ("R is 5 == 5.", "R = true.\n"),
    ("R is 5 == 6.", "R = false.\n"),
    ("B is prelude:true().", "B = true.\n"),
    ("B is prelude:false().", "B = false.\n"),
    ("X = true, X == (5 == 5).", "X = true.\n"),
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
