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
    # :info / :i — inspect a single identifier. Examples cover the four
    # output categories: built-in type, function (with `requiring`),
    # data constructor (rendered as the parent type's declaration),
    # the unknown-name fallback, and arity disambiguation. The bare
    # `call` case asserts that omitting the arity emits both blocks
    # blank-line separated.
    (":info int", "'$typechecker':int\nbuilt-in type\n"),
    (
        ":info max",
        "prelude:max\n"
        ":- function max(T, T) -> T requiring '>='(T, T) -> bool.\n",
    ),
    (
        ":info true",
        "prelude:true\n:- chr_type bool ---> true ; false.\n",
    ),
    (":info foo", "unknown identifier: foo\n"),
    (
        ":info call/2",
        "prelude:call\n:- function call(fun(A) -> B end, A) -> B.\n",
    ),
    (
        ":info call/3",
        "prelude:call\n:- function call(fun(A, B) -> C end, A, B) -> C.\n",
    ),
    (
        ":info call",
        "prelude:call\n"
        ":- function call(fun(A) -> B end, A) -> B.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B) -> C end, A, B) -> C.\n",
    ),
    (
        ":i nl",
        "prelude:nl\n:- function nl() -> any.\n",
    ),
    (
        ":info '+'",
        "prelude:'+'\n"
        ":- class\n"
        "    ('+'(float, float) -> float),\n"
        "    ('+'(int, int) -> int).\n",
    ),
    (
        ":info prelude:max",
        "prelude:max\n"
        ":- function max(T, T) -> T requiring '>='(T, T) -> bool.\n",
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


def test_info_hidden_constructors(ychr_bin, tmp_path):
    """A data constructor that is not exported by its parent type's
    module is invisible to `:info NAME` (returns "unknown identifier"),
    even when its parent type is itself exported. Three flavors are
    exercised: a fully-exported type (both ctors visible), a
    partially-exported type (`type(partial/0, [shown])` hides `hidden`),
    and a type left out of the export list entirely (both ctors hidden).
    The parent type's declaration body still lists every constructor —
    only direct lookup is filtered."""
    (tmp_path / "info_hidden.chr").write_text(
        ":- module(info_hidden, [\n"
        "    type(visible/0),\n"
        "    type(partial/0, [shown]),\n"
        "    use_visible/0\n"
        "]).\n"
        ":- chr_type visible ---> public ; alsopublic.\n"
        ":- chr_type partial ---> shown ; hidden.\n"
        ":- chr_type allhidden ---> totally ; secret.\n"
        ":- chr_constraint use_visible/0.\n"
        "use_visible <=> true.\n"
    )
    queries = [
        ":info public",  # exported via type(visible/0) → all cons visible
        ":info shown",  # exported via type(partial/0, [shown])
        ":info hidden",  # in partial but not in explicit list → hidden
        ":info totally",  # parent type not in exports at all → hidden
        ":info info_hidden:secret",  # qualified hidden ctor stays hidden
        ":info partial",  # type itself: body still lists both ctors
    ]
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", str(tmp_path / "info_hidden.chr")],
        input="\n".join(queries) + "\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    expected = (
        "info_hidden:public\n"
        ":- chr_type visible ---> public ; alsopublic.\n"
        "info_hidden:shown\n"
        ":- chr_type partial ---> shown ; hidden.\n"
        "unknown identifier: hidden\n"
        "unknown identifier: totally\n"
        "unknown identifier: info_hidden:secret\n"
        "info_hidden:partial\n"
        ":- chr_type partial ---> shown ; hidden.\n"
    )
    assert result.stdout == expected


def test_info_cross_module_ambiguity(ychr_bin, tmp_path):
    """Two modules exporting the same `(name, arity)` make `:info NAME`
    refuse to guess. The user's documented choice is to error and list
    the candidate modules; qualifying with `mod:name` then succeeds."""
    (tmp_path / "amb1.chr").write_text(
        ":- module(amb1, [twin/1]).\n:- chr_constraint twin/1.\n"
    )
    (tmp_path / "amb2.chr").write_text(
        ":- module(amb2, [twin/1]).\n:- chr_constraint twin/1.\n"
    )
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", str(tmp_path / "amb1.chr"), str(tmp_path / "amb2.chr")],
        input=":info twin\n:info amb1:twin\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    # The order of the listed modules follows iteration order over
    # `exportMap`'s `AmbiguousExport`, which is the order the modules
    # were parsed in. The qualified lookup then succeeds on amb1.
    assert "ambiguous identifier: twin/1 is exported by" in result.stdout
    assert "amb1" in result.stdout and "amb2" in result.stdout
    assert "amb1:twin\n:- chr_constraint twin(any).\n" in result.stdout
