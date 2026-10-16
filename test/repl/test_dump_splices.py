"""Integration tests for ``--dump-splices``.

The flag prints the clauses ``:- macro_decls`` uses spliced into the input
files, to stderr, on every command that compiles files. Goal macros expand
later, in the renamer, and are never in the dump. See docs/reference/macros.md.
"""

import subprocess

PROGRAM = (
    ":- module(m).\n"
    ":- chr_constraint go/0.\n"
    "go <=> true.\n"
    ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].\n"
    ":- flag(on).\n"
)

# The declaration macro's use is at line 5 col 1; the user-written clauses
# (`go <=> true.`) are not part of the dump. The header names the file as
# it was given on the command line, and clauses go through the same
# pretty-printer as diagnostics, so `/` comes out spaced.
def expected_dump(program):
    return (
        f"% splices for {program} (module m)\n"
        f"% m:flag/1 at {program}:5:1\n"
        ":- chr_constraint on / 0.\n"
    )

GOAL_MACRO_PROGRAM = (
    ":- module(g).\n"
    ":- chr_constraint a/0, b/0.\n"
    ":- macro m ---> [b].\n"
    "a ==> m.\n"
)

# A declaration-macro use that expands fine, plus a directive that is not
# a built-in and not a macro: expansion succeeds, then fails, so the
# compile as a whole produces no program and no dump.
BROKEN_PROGRAM = PROGRAM + ":- not_a_directive.\n"


def write(tmp_path, text, name="m.chr"):
    path = tmp_path / name
    path.write_text(text)
    return path


def test_compile_dumps_splices_to_stderr(ychr_bin, tmp_path):
    """`compile --dump-splices` reports the splice on stderr and leaves
    stdout to the generated path."""
    program = write(tmp_path, PROGRAM)
    out = tmp_path / "out"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(out), "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert result.stderr == expected_dump(program)
    assert result.stdout.strip() == str(out / "program.vm")


def test_compile_without_flag_dumps_nothing(ychr_bin, tmp_path):
    """Without the flag, stderr stays as quiet as it was."""
    program = write(tmp_path, PROGRAM)
    out = tmp_path / "out"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(out), str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert result.stderr == ""


def test_failed_compile_dumps_nothing(ychr_bin, tmp_path):
    """A compile that fails before producing a program prints the error,
    not a partial dump."""
    program = write(tmp_path, BROKEN_PROGRAM)
    out = tmp_path / "out"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(out), "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "splices for" not in result.stderr
    assert "on / 0" not in result.stderr


def test_goal_macro_is_not_dumped(ychr_bin, tmp_path):
    """A program whose only macro is a goal macro produces no dump."""
    program = write(tmp_path, GOAL_MACRO_PROGRAM, "g.chr")
    out = tmp_path / "out"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "vm", "-d", str(out), "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert result.stderr == ""


def test_check_accepts_dump_splices(ychr_bin, tmp_path):
    """`check` compiles the program, so it accepts the flag too."""
    program = write(tmp_path, PROGRAM)
    result = subprocess.run(
        [ychr_bin, "check", "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"check failed:\n{result.stdout}\n{result.stderr}"
    assert expected_dump(program) in result.stderr


def test_scheme_target_accepts_dump_splices(ychr_bin, tmp_path):
    """`compile -t scheme` dumps too; the runtime note is separate."""
    program = write(tmp_path, PROGRAM)
    out = tmp_path / "out"
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(out), "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"
    assert expected_dump(program) in result.stderr


def test_run_accepts_dump_splices(ychr_bin, tmp_path):
    """`run` dumps on stderr; the goal's own output stays on stdout."""
    program = write(tmp_path, PROGRAM)
    result = subprocess.run(
        [ychr_bin, "run", "-g", "go", "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"run failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout == ""
    assert expected_dump(program) in result.stderr


def test_gen_driver_accepts_dump_splices(ychr_bin, tmp_path):
    """`gen-driver` dumps on stderr; the driver source stays on stdout."""
    program = write(tmp_path, PROGRAM)
    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", "go", "--dump-splices", str(program)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"gen-driver failed:\n{result.stdout}\n{result.stderr}"
    assert result.stdout != ""
    assert expected_dump(program) in result.stderr


def test_repl_accepts_dump_splices(ychr_bin, tmp_path):
    """The dump is explicit, so `--quiet` does not suppress it."""
    program = write(tmp_path, PROGRAM)
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", "--dump-splices", str(program)],
        input=":quit\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert expected_dump(program) in result.stderr


def test_repl_recompile_dumps_again(ychr_bin, tmp_path):
    """:recompile compiles again, so it dumps again."""
    program = write(tmp_path, PROGRAM)
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet", "--dump-splices", str(program)],
        input=":recompile\n:quit\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert result.stderr.count("% splices for") == 2
