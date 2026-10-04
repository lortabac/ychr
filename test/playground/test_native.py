"""The playground bridge, exercised through its native harness.

``playground/Main.hs`` drives ``YCHR.Playground`` — the module the WASM
entry point wraps — over a command protocol on stdin, so the bridge's
behaviour is testable without emscripten, a browser or a Node install. The
same :mod:`expectations` table asserts the WASM module in
``test_wasm.py``.

The resource root is the project directory, so the harness finds
``libraries/`` and ``typechecker/`` exactly as ``YCHR_LIB_DIR`` describes
them.
"""

import os
import subprocess

import expectations

TIMEOUT = 1800


def run_commands(playground_bin, commands):
    """Run harness commands and return the list of ``(status, payload)``.

    ``LC_ALL`` is pinned because the scenario includes non-ASCII output and
    GHC encodes its handles from the locale: under a C/POSIX locale the
    harness would fail on a character it cannot encode, which says nothing
    about the playground.
    """
    env = dict(
        os.environ, YCHR_LIB_DIR=expectations.PROJECT_ROOT, LC_ALL="C.UTF-8"
    )
    proc = subprocess.run(
        [playground_bin],
        input="\n".join(commands) + "\n:quit\n",
        capture_output=True,
        text=True,
        cwd=expectations.PROJECT_ROOT,
        env=env,
        timeout=TIMEOUT,
    )
    assert proc.returncode == 0, f"harness failed:\n{proc.stderr}"
    responses = []
    for chunk in proc.stdout.split("\n---\n"):
        if not chunk.strip():
            continue
        status, _, payload = chunk.partition("\n\n")
        responses.append((status, payload))
    return responses


def run_scenario(playground_bin):
    """Replay the shared scenario and return ``label -> (status, payload)``."""
    responses = run_commands(playground_bin, expectations.native_commands())
    assert len(responses) == len(expectations.LABELS), (
        f"expected {len(expectations.LABELS)} responses, got "
        f"{len(responses)}"
    )
    return dict(zip(expectations.LABELS, responses))


def test_colon_commands(playground_bin):
    """The page's colon commands answer the way the terminal REPL's do.

    ``:h`` is the alias the terminal REPL documents for ``:help``, so it
    must print the help text rather than nothing.
    """
    responses = run_commands(playground_bin, [":help", ":h", ":list_files"])
    for status, payload in responses:
        assert status == "ok", payload
    assert "Commands:" in responses[0][1], responses[0][1]
    assert "Commands:" in responses[1][1], responses[1][1]
    assert "editor.chr" in responses[2][1], responses[2][1]


def test_scenario(playground_bin):
    """The shared scenario passes on the native bridge."""
    expectations.check(run_scenario(playground_bin))


def test_reload_keeps_the_previous_program(playground_bin):
    """A failing reload keeps the last good program, and says so."""
    results = run_scenario(playground_bin)
    # `query-after-failed-reload` is the assertion that matters, and it is
    # in the shared table; this pins the extra detail that the diagnostic
    # names the synthetic file the editor compiles as.
    assert "editor.chr" in results["compile-broken"][1]


def test_unknown_command(playground_bin):
    """A colon command the page does not implement is rejected politely."""
    responses = run_commands(
        playground_bin, [f":load {expectations.STARTER}", ":nope"]
    )
    status, payload = responses[1]
    assert status == "error", payload
    assert "Unknown command: :nope" in payload, payload


def test_missing_file_is_reported(playground_bin):
    """A reload of a file that does not exist is an error response, not a crash."""
    responses = run_commands(playground_bin, [":load does-not-exist.chr"])
    status, payload = responses[0]
    assert status == "error", payload
    assert "does-not-exist.chr" in payload, payload


def test_typecheck_reports_type_errors(playground_bin):
    """`Typecheck` answers with an error when the program is ill-typed.

    ``float_type_error`` is a golden program whose rule body adds an ``int``
    to a ``float``; the whole-program check reports it as YCHR-60006. The
    reload itself must still succeed — type checking is a separate step, as
    the page's two buttons imply.
    """
    program = os.path.join(
        expectations.PROJECT_ROOT,
        "test",
        "golden",
        "float_type_error",
        "float_type_error.chr",
    )
    responses = run_commands(playground_bin, [f":load {program}", ":check"])
    assert responses[0][0] == "ok", responses[0][1]
    status, payload = responses[1]
    assert status == "error", payload
    assert "YCHR-60006" in payload, payload
