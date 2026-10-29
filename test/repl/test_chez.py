"""Integration tests for the Chez REPL backend.

The tests skip when no Chez executable is available. They set
``YCHR_SCHEME_LIB_DIR`` to the checkout's ``scheme/`` directory so the
backend does not depend on the test's working directory.
"""

import os
import re
import shutil
import subprocess

import pytest


def _scheme_command():
    return os.environ.get("YCHR_SCHEME", "scheme")


@pytest.fixture(scope="session")
def chez_env(project_root):
    command = _scheme_command()
    if shutil.which(command) is None:
        pytest.skip(f"no Chez Scheme executable found (tried {command})")
    return {
        **os.environ,
        "YCHR_SCHEME": command,
        "YCHR_SCHEME_LIB_DIR": os.path.join(project_root, "scheme"),
    }


def run_repl(ychr_bin, program, input_text, env, *flags):
    args = [ychr_bin, "repl", "--repl-backend=chez", "--quiet", *flags]
    if program is not None:
        args.append(str(program))
    return subprocess.run(
        args,
        input=input_text,
        capture_output=True,
        text=True,
        env=env,
    )


def run_interpreter(ychr_bin, program, input_text, env, *flags):
    args = [ychr_bin, "repl", "--quiet", *flags]
    if program is not None:
        args.append(str(program))
    return subprocess.run(
        args,
        input=input_text,
        capture_output=True,
        text=True,
        env=env,
    )


def assert_parity(ychr_bin, program, input_text, env):
    chez = run_repl(ychr_bin, program, input_text, env)
    interpreter = run_interpreter(ychr_bin, program, input_text, env)
    assert chez.returncode == interpreter.returncode, (
        f"return codes differ\nchez stdout:\n{chez.stdout}\n"
        f"chez stderr:\n{chez.stderr}\n"
        f"interpreter stdout:\n{interpreter.stdout}\n"
        f"interpreter stderr:\n{interpreter.stderr}"
    )
    assert chez.stdout == interpreter.stdout, (
        f"stdout differs\nchez:\n{chez.stdout}\ninterpreter:\n{interpreter.stdout}\n"
        f"chez stderr:\n{chez.stderr}"
    )
    assert chez.stderr == interpreter.stderr, (
        f"stderr differs\nchez:\n{chez.stderr}\ninterpreter:\n{interpreter.stderr}"
    )


def write_program(tmp_path, name, text):
    path = tmp_path / name
    path.write_text(text)
    return path


def test_basic_query(ychr_bin, chez_env):
    result = run_repl(ychr_bin, None, "R is 1 + 1.\n:quit\n", chez_env)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == "R = 2.\n"


def test_query_lambda_and_aliases(ychr_bin, chez_env):
    result = run_repl(
        ychr_bin,
        None,
        (
            "R is '$call'(fun(X) -> X + 1 end, 1).\n"
            "X = 1, Y = X.\n"
            ":quit\n"
        ),
        chez_env,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == "R = 2.\nX = 1,\nY = 1.\n"


def test_query_lambda_captures_query_var(ychr_bin, chez_env):
    result = run_repl(
        ychr_bin,
        None,
        "Y = 10, R is '$call'(fun(X) -> X + Y end, 1).\n:quit\n",
        chez_env,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == "R = 11,\nY = 10.\n"


def test_program_constraint(ychr_bin, tmp_path, chez_env):
    program = write_program(
        tmp_path,
        "p.chr",
        ":- module(p, [go/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint go(any).\n"
        "go(R) <=> R is 1 + 1.\n",
    )
    result = run_repl(ychr_bin, program, "go(R).\n:quit\n", chez_env)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == "R = 2.\n"


def test_dynamic_tell_parity(ychr_bin, tmp_path, chez_env):
    program = write_program(
        tmp_path,
        "succ_m.chr",
        ":- module(succ_m, [succ/2]).\n"
        ":- chr_constraint succ/2, hidden/1.\n"
        "succ(X, R) <=> R is X + 1.\n",
    )
    query = (
        "tell(succ(1, R)).\n"
        "tell(quote(succ), 3, R).\n"
        "tell(quote(succ_m:succ(4)), R).\n"
        "tell(quote(hidden(1))).\n"
        "tell(G).\n"
        ":quit\n"
    )
    assert_parity(ychr_bin, program, query, chez_env)


def test_live_store_parity(ychr_bin, tmp_path, chez_env):
    program = write_program(
        tmp_path,
        "store.chr",
        ":- module(store, [p/1]).\n"
        ":- chr_constraint p/1.\n",
    )
    query = ":begin\np(1).\np(2).\nprint_store.\n:end\n:quit\n"
    assert_parity(ychr_bin, program, query, chez_env)


def test_runtime_error_parity(ychr_bin, chez_env):
    assert_parity(ychr_bin, None, "1 = 2.\n:quit\n", chez_env)


def test_live_runtime_error_aborts(ychr_bin, chez_env):
    assert_parity(ychr_bin, None, ":begin\n1 = 2.\n:quit\n", chez_env)


def test_live_lambda_is_recoverable(ychr_bin, chez_env):
    query = (
        ":begin\n"
        "R is '$call'(fun(X) -> X + 1 end, 1).\n"
        ":end\n"
        ":quit\n"
    )
    assert_parity(ychr_bin, None, query, chez_env)


def test_time(ychr_bin, chez_env):
    result = run_repl(ychr_bin, None, ":time R is 1 + 1.\n:quit\n", chez_env)
    assert result.returncode == 0, result.stdout + result.stderr
    assert re.fullmatch(r"Time: \d+\.\d{6}s\nR = 2\.\n", result.stdout), result.stdout


def test_trace_is_rejected(ychr_bin, chez_env):
    result = run_repl(ychr_bin, None, ":trace R is 1 + 1.\n:quit\n", chez_env)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == ""
    assert ":trace is not available with --repl-backend=chez" in result.stderr


def test_recompile_restarts_backend(ychr_bin, tmp_path, chez_env):
    program = write_program(
        tmp_path,
        "recompile.chr",
        ":- module(rc, [p/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint p(any).\n"
        "p(R) <=> R is 1.\n",
    )
    result = run_repl(
        ychr_bin,
        program,
        "p(R).\n:recompile\np(R).\n:quit\n",
        chez_env,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == "R = 1.\nR = 1.\n"


def test_missing_runtime_is_reported(ychr_bin, tmp_path, chez_env):
    env = dict(chez_env)
    env.pop("YCHR_SCHEME_LIB_DIR", None)
    result = subprocess.run(
        [ychr_bin, "repl", "--repl-backend=chez", "--quiet"],
        input=":quit\n",
        capture_output=True,
        text=True,
        cwd=tmp_path,
        env=env,
    )
    assert result.returncode != 0
    assert "cannot find the YCHR Scheme runtime" in result.stderr


def test_missing_scheme_is_reported(ychr_bin, tmp_path, chez_env):
    env = dict(chez_env)
    env.pop("YCHR_SCHEME", None)
    env.pop("PATH", None)
    result = subprocess.run(
        [ychr_bin, "repl", "--repl-backend=chez", "--quiet"],
        input=":quit\n",
        capture_output=True,
        text=True,
        cwd=tmp_path,
        env=env,
    )
    assert result.returncode != 0
    assert "cannot find the Chez Scheme executable" in result.stderr


def test_unknown_backend_is_a_usage_error(ychr_bin):
    result = subprocess.run(
        [ychr_bin, "repl", "--repl-backend=bogus"],
        input="",
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "Unknown REPL backend" in result.stderr
