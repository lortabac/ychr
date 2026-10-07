"""REPL integration tests.

Most tests pipe a query into ``ychr repl --quiet`` and check stdout; a
few drive other modes and check stderr. To add a new test, append a
(query, expected_output) tuple to REPL_TESTS.
"""

import os
import re
import subprocess

import pytest


def runtime_error(message):
    """Expected stdout for a query that raises a runtime error.

    Query-side runtime errors render through the same coded-diagnostic
    envelope as errors raised from a rule body (YCHR-60001), rather than
    a bare one-line message.
    """
    return (
        "\x1b[95m=== runtime error ===\x1b[0m\n"
        f"\x1b[1m<generated>:1:1: YCHR-60001\n{message}\n\x1b[0m"
    )


REPL_TESTS = [
    ("R is 1 + 1.", "R = 2.\n"),
    ("R is '$call'(fun(X) -> X end, 1).", "R = 1.\n"),
    ("R is '$call'(fun(X) -> X + 1 end, 1).", "R = 2.\n"),
    ("R is '$call'(fun(X, _) -> X end, 1, _).", "R = 1.\n"),
    ("R is '$call'(fun(X, Y, Z) -> X + Y + Z end, 1, 2, 3).", "R = 6.\n"),
    ("R is call(fun(A, B, C, D) -> A + B + C + D end, 1, 2, 3, 4).", "R = 10.\n"),
    (
        "R is call(fun(A, B, C, D, E, F, G, H, I, J) -> A + B + C + D + E + F + G + H + I + J end, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10).",
        "R = 55.\n",
    ),
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
    # A string spelling `fun name/arity` reads as a first-class function
    # reference, so the prelude's `call/N` can apply it. The binding
    # printer renders the closure in its flat form, as it does for a
    # source `fun '+'/2`.
    (
        'F is read_term_from_string("fun \'+\'/2"), R is call(F, 1, 1).',
        "F = 'prelude:+' / 2,\nR = 2.\n",
    ),
    # Any `fun name/arity` term built at run time is callable too: the
    # `'$call'` dispatch site resolves the flat name, so the term keeps
    # its surface shape while `call/N` applies it.
    (
        "F is list_to_compound([quote('fun'), "
        "list_to_compound([quote('/'), quote('+'), 2])]), R is call(F, 1, 1).",
        "F = fun '+' / 2,\nR = 2.\n",
    ),
    ("R is member(1, []).", "R = false.\n"),
    ("R is member(1, [1]).", "R = true.\n"),
    ("R is member(1, [1, 2]).", "R = true.\n"),
    ("R is member(1, [0, 1, 2]).", "R = true.\n"),
    ("R is member(1, [0, 2]).", "R = false.\n"),
    ("R is compound_to_list(quote(1 + 1)).", "R = ['+', 1, 1].\n"),
    ("R is copy_term(quote(foo(X))), X = 1.", "R = foo(_),\nX = 1.\n"),
    # Synthetic qualified atoms (no real module `foo`) require the
    # `quote/1` opt-out: the renamer treats `quote(X)` as fully opaque
    # data, so no module-visibility check fires on the qualified
    # `:`-compound inside.
    ("host:print(quote(':'(foo, bar))).", "foo:bar\n"),
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
    ("1 = 2.", runtime_error("unification failure: cannot unify 1 with 2")),
    (
        "[X, Y] = [1, 2, 3].",
        runtime_error("unification failure: cannot unify [1, 2] with [1, 2, 3]"),
    ),
    # :info / :i — inspect a single identifier. Examples cover the four
    # output categories: built-in type, function (with `requiring` or
    # `refining`), data constructor (rendered as the parent type's
    # declaration), the unknown-name fallback, and arity
    # disambiguation. The bare `call` case asserts that omitting the
    # arity emits both blocks blank-line separated.
    (":info int", "'$typechecker':int\nbuilt-in type\n"),
    (
        ":info max",
        "prelude:max\n"
        ":- function max(T, T) -> T requiring '>='(T, T) -> bool.\n",
    ),
    (
        ":info integer",
        "prelude:integer\n:- function integer(any) -> bool refining int.\n",
    ),
    (
        ":info true",
        "prelude:true\n:- chr_type bool ---> true ; false.\n",
    ),
    (":info foo", "unknown identifier: foo\n"),
    (
        ":info call/11",
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F, G, H, I, J) -> K end,"
        " A, B, C, D, E, F, G, H, I, J) -> K.\n",
    ),
    (
        ":info call",
        "prelude:call\n"
        ":- function call(fun(A) -> B end, A) -> B.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B) -> C end, A, B) -> C.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C) -> D end, A, B, C) -> D.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D) -> E end, A, B, C, D) -> E.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E) -> F end, A, B, C, D, E) -> F.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F) -> G end, A, B, C, D, E, F) -> G.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F, G) -> H end, A, B, C, D, E, F, G) -> H.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F, G, H) -> I end, A, B, C, D, E, F, G, H) -> I.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F, G, H, I) -> J end, A, B, C, D, E, F, G, H, I) -> J.\n"
        "\n"
        "prelude:call\n"
        ":- function call(fun(A, B, C, D, E, F, G, H, I, J) -> K end,"
        " A, B, C, D, E, F, G, H, I, J) -> K.\n",
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
    # :trace — refined-operational-semantics tracer. The arithmetic
    # case shows that user-function entries (`call prelude:+`), host
    # calls (`host call +`), and returns are all visible. Bindings are
    # intentionally not printed; the user re-runs without `:trace` to
    # see them. The bare `:trace` form prints a usage line.
    (
        ":trace R is 1 + 2.",
        "call prelude:+(1, 2)\n  host call +(1, 2) = 3\nreturn 3\n",
    ),
    # Query-side `=` and host-call goals go through `Run.executeBodyGoal`,
    # which has its own trace instrumentation parallel to the
    # interpreter's `BUnify` / `invokeHostCall` paths. A `=` against a
    # ground RHS produces a single `unify` event with no reactivations
    # (no constraints are watching an unbound variable yet).
    (
        ":trace X = 1.",
        "unify _ = 1\n",
    ),
    (
        ":trace host:print(42).",
        "42\nhost call print(42) = '()'\n",
    ),
    (
        ":trace",
        ":trace GOAL  -- run GOAL with refined-operational-semantics tracing\n",
    ),
    # A `%` comment at the end of a line is stripped before the query is
    # parsed, matching the file grammar (docs/reference/language.md): the
    # period still terminates the goal, so the query runs.
    ("X = 1. % trailing comment", "X = 1.\n"),
    # A `%` inside a string literal is data, not a comment: only the text
    # after the closing quote is dropped.
    ('X = "% done". % trailing comment', 'X = "% done".\n'),
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


def test_repl_query_warning_snippet(ychr_bin):
    """A query warning echoes the query's own source term, not `''`.

    Regression: the renamer anchored query terms at the `<generated>`
    dummy location with an empty `Atom ""` origin, so the diagnostic's
    source snippet rendered as the empty-quotes `''`. Query diagnostics
    now use `<query>` and reconstruct the term from itself.
    """
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input="B is atom(foo).\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert "YCHR-20101" in result.stderr, result.stderr
    assert "<query>:1:1" in result.stderr, result.stderr
    assert "B is atom(foo)" in result.stderr, result.stderr
    assert "''" not in result.stderr, result.stderr


def test_repl_unsupported_call_arity(ychr_bin):
    """A query whose `$call` is outside the supported 1..10 arity range
    is rejected by the resolver (YCHR-16022) rather than becoming a data
    term. The range is the surface-language limit, aligned with the
    prelude's `call/N` family."""
    for query, given in [
        # One argument is the callee, so this applies it to nothing.
        ("R is '$call'(fun(A) -> A end).", 0),
        (
            "R is '$call'(fun(A, B, C, D, E, F, G, H, I, J, K) -> A end,"
            " 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11).",
            11,
        ),
    ]:
        result = subprocess.run(
            [ychr_bin, "repl", "--quiet"],
            input=query + "\n",
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
        assert "YCHR-16022" in result.stdout, result.stdout
        assert (
            f"'$call' takes between 1 and 10 arguments, but was given {given}"
            in result.stdout
        ), result.stdout


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


def test_trace_chr_program(ychr_bin, tmp_path):
    """`:trace` against a CHR program shows the ωr events for a single
    propagation rule fire: tell, activate, try-occurrence, partner
    pick, fire (with constraint ids), store, and recursive tell.
    Tests the core CHR scheduling events together (function/host-call
    events are tested by the inline arithmetic case). Store events
    appear where Late Storage actually stores: before the body of a
    fired rule that keeps the constraint, or at the end of an
    activation the constraint survived — never right after the tell."""
    (tmp_path / "prop.chr").write_text(
        ":- module(prop, [p/1, q/1]).\n"
        ":- chr_constraint p/1.\n"
        ":- chr_constraint q/1.\n"
        "make_q @ p(X) ==> q(X).\n"
    )
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", str(tmp_path / "prop.chr")],
        input=":trace prop:p(1).\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    expected = (
        "tell prop:p(1)\n"
        "  activate c#0: prop:p(1)\n"
        "    try occurrence prop:p #1 (rule make_q)\n"
        "      fire make_q [c#0]\n"
        "      store c#0: prop:p(1)\n"
        "      tell prop:q(1)\n"
        "        activate c#1: prop:q(1)\n"
        "          store c#1: prop:q(1)\n"
    )
    assert result.stdout == expected


def test_trace_nested_foreach(ychr_bin, tmp_path):
    """`:trace` on a multi-head rule shows nested `Foreach` iterations
    indented: each inner partner sits one level deeper than the outer.
    A 3-head propagation rule compiles to two nested Foreaches (one
    per non-active partner); the last-told constraint activates against
    a fully-populated store and triggers the fire."""
    (tmp_path / "nest.chr").write_text(
        ":- module(nest, [a/1, b/1, c/1, ok/0]).\n"
        ":- chr_constraint a/1.\n"
        ":- chr_constraint b/1.\n"
        ":- chr_constraint c/1.\n"
        ":- chr_constraint ok/0.\n"
        "r @ a(X), b(X), c(X) ==> ok.\n"
    )
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", str(tmp_path / "nest.chr")],
        input=":trace nest:a(1), nest:b(1), nest:c(1).\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    expected = (
        "tell nest:a(1)\n"
        "  activate c#0: nest:a(1)\n"
        "    try occurrence nest:a #1 (rule r)\n"
        "    store c#0: nest:a(1)\n"
        "tell nest:b(1)\n"
        "  activate c#1: nest:b(1)\n"
        "    try occurrence nest:b #1 (rule r)\n"
        "    store c#1: nest:b(1)\n"
        "tell nest:c(1)\n"
        "  activate c#2: nest:c(1)\n"
        "    try occurrence nest:c #1 (rule r)\n"
        "      partner c#1: nest:b(1)\n"
        "        partner c#0: nest:a(1)\n"
        "          fire r [c#2, c#1, c#0]\n"
        "          store c#2: nest:c(1)\n"
        "          tell nest:ok\n"
        "            activate c#3: nest:ok\n"
        "              store c#3: nest:ok\n"
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


def test_repl_history_unavailable_degrades(ychr_bin, tmp_path):
    """An unusable history location must not abort startup. The REPL runs
    with history disabled and reports it once on stderr; `--quiet` drops
    the report but still runs. Three unusable layouts are exercised: the
    data directory cannot be created, the history path is itself a
    directory, and the history file is read-only. The first two are
    root-proof, so only the read-only file case is skipped for root."""
    notice = "REPL history not available"

    def run(data_dir, *args):
        return subprocess.run(
            [ychr_bin, "repl", *args],
            input="R is 1 + 1.\n",
            capture_output=True,
            text=True,
            env={**os.environ, "XDG_DATA_HOME": str(data_dir)},
        )

    # The data directory cannot be created: XDG_DATA_HOME points below a
    # regular file, so createDirectoryIfMissing fails with ENOTDIR.
    blocker = tmp_path / "blocker"
    blocker.write_text("not a directory")
    loud = run(blocker / "sub")
    assert loud.returncode == 0, f"repl failed:\n{loud.stdout}\n{loud.stderr}"
    assert loud.stderr.count(notice) == 1, loud.stderr
    assert notice not in loud.stdout
    assert "R = 2." in loud.stdout

    quiet = run(blocker / "sub", "--quiet")
    assert quiet.returncode == 0, f"repl failed:\n{quiet.stdout}\n{quiet.stderr}"
    assert quiet.stderr == ""
    assert quiet.stdout == "R = 2.\n"

    # The history path is a directory: its parent is fine, but the probe
    # cannot open the path for writing.
    as_dir = tmp_path / "as_dir"
    (as_dir / "ychr" / "history").mkdir(parents=True)
    dir_loud = run(as_dir)
    assert dir_loud.returncode == 0, f"repl failed:\n{dir_loud.stdout}\n{dir_loud.stderr}"
    assert dir_loud.stderr.count(notice) == 1, dir_loud.stderr
    assert notice not in dir_loud.stdout
    assert "R = 2." in dir_loud.stdout

    # Permission-bit layouts. Root bypasses them, so these cases are
    # skipped when running as root. The read-only file fails the
    # AppendMode probe; the write-only file passes it and fails the
    # ReadMode probe, so both halves of `ensureUsable` are exercised.
    if hasattr(os, "geteuid") and os.geteuid() != 0:
        for label, mode in [("read_only", 0o444), ("write_only", 0o200)]:
            case = tmp_path / label
            (case / "ychr").mkdir(parents=True)
            history = case / "ychr" / "history"
            history.write_text("")
            os.chmod(history, mode)
            result = run(case)
            assert result.returncode == 0, (
                f"{label}: repl failed:\n{result.stdout}\n{result.stderr}"
            )
            assert result.stderr.count(notice) == 1, result.stderr
            assert notice not in result.stdout
            assert "R = 2." in result.stdout

    # A usable location reports nothing on stderr and creates the file.
    data = tmp_path / "data"
    writable = run(data)
    assert writable.returncode == 0, f"repl failed:\n{writable.stdout}\n{writable.stderr}"
    assert writable.stderr == ""
    assert "R = 2." in writable.stdout
    assert (data / "ychr" / "history").exists()


def test_repl_time(ychr_bin):
    """`:time` prints the query's execution time before the bindings.
    The value is nondeterministic, so only its shape is asserted: the
    literal label and unit, six decimals, microseconds resolution. The
    bare form prints a usage line, like `:trace`."""
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=":time R is 1 + 2.\n:time\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert re.fullmatch(
        r"Time: \d+\.\d{6}s\n"
        r"R = 3\.\n"
        r":time GOAL  -- run GOAL and print its execution time in seconds\n",
        result.stdout,
    ), result.stdout


def test_repl_time_failure(ychr_bin):
    """The timing line's placement relative to failures. A runtime
    error follows the timing line, because execution started and was
    measured; a query rejected during preparation (here an unknown
    predicate, YCHR-30001) prints no timing line, because nothing was
    executed."""
    runtime = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=":time 1 = 2.\n",
        capture_output=True,
        text=True,
    )
    assert runtime.returncode == 0, f"repl failed:\n{runtime.stdout}\n{runtime.stderr}"
    assert re.fullmatch(
        r"Time: \d+\.\d{6}s\n"
        + re.escape(runtime_error("unification failure: cannot unify 1 with 2")),
        runtime.stdout,
    ), runtime.stdout

    prep = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=":time no_such_constraint.\n",
        capture_output=True,
        text=True,
    )
    assert prep.returncode == 0, f"repl failed:\n{prep.stdout}\n{prep.stderr}"
    assert "YCHR-30001" in prep.stdout, prep.stdout
    assert "Time:" not in prep.stdout, prep.stdout


def test_compile_vm_creates_output_dirs(ychr_bin, tmp_path):
    """`compile -t vm` creates the output directory before writing,
    mirroring the Scheme target's `createDirectoryIfMissing`. Two
    layouts exercise the call: a missing `-d DIR` whose parents do not
    exist either, and a `-n` base name that itself contains a
    subdirectory. Without it, `writeFile` raises an uncaught
    `IOException` instead of compiling."""
    program = tmp_path / "w.chr"
    program.write_text(
        ":- module(w, [go/1]).\n"
        ":- chr_constraint go/1.\n"
        "go(X) <=> X = 1.\n"
    )

    # A missing -d directory, including its parents. The default base
    # name is `program`.
    out_dir = tmp_path / "nested" / "deeper"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(out_dir), str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert (out_dir / "program.vm").exists()

    # A -n base name carrying its own subdirectory, resolved under -d.
    named_dir = tmp_path / "named"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(named_dir), "-n", "sub/w", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert (named_dir / "sub" / "w.vm").exists()


def test_repl_comment_only_line(ychr_bin):
    """A line holding only a `%` comment vanishes: it becomes an empty
    line, which the loop already skips, so the following goal runs. The
    `%` is otherwise a parse error, since the REPL only sees raw lines."""
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input="% only a comment\nX = 1.\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout == "X = 1.\n"


def test_repl_crlf_input(ychr_bin):
    """CRLF line endings are tolerated: the trailing `\\r` is trimmed
    before the line is dispatched, so `:quit\\r` exits. Previously the
    `\\r` made the command fall through to the query parser, which
    failed on `:quit\\r` after the preceding goal had already run."""
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input="X = 1.\r\n:quit\r\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout == "X = 1.\n"


def test_repl_live_session_comment_and_crlf(ychr_bin):
    """The live session normalizes its own input with the same helper:
    a trailing comment and a CRLF ending are stripped there too, and
    `:end\\r` ends the session cleanly instead of being parsed as a
    goal."""
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=":begin\nX = 1. % trailing comment\r\n:end\r\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout == "X = 1.\n"
