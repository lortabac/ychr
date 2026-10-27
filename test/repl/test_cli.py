"""Top-level CLI parsing tests.

The default mode (no subcommand) takes no flags, so a flag before a
subcommand is a usage error.
"""

import subprocess

import pytest

NO_FLAGS_BEFORE_SUBCOMMAND = [
    ["--quiet", "repl"],
    ["--quiet", "check"],
    ["--Werror", "run", "-g", "x"],
    ["--dump-splices", "check"],
]


@pytest.mark.parametrize("args", NO_FLAGS_BEFORE_SUBCOMMAND, ids=lambda a: " ".join(a))
def test_flag_before_subcommand_is_rejected(ychr_bin, args):
    result = subprocess.run(
        [ychr_bin, *args],
        input="",
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "Invalid option" in result.stderr
    assert "Uncaught exception" not in result.stderr


def test_flag_after_subcommand_still_works(ychr_bin):
    result = subprocess.run(
        [ychr_bin, "repl", "--quiet"],
        input=":quit\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"repl failed:\n{result.stdout}\n{result.stderr}"
    assert "ychr>" not in result.stdout, "--quiet should drop the prompt"


PROGRAM = (
    ":- module(default_mode).\n"
    ":- chr_constraint go/0.\n"
    "go <=> true.\n"
)


def test_default_mode_takes_a_bare_file(ychr_bin, tmp_path):
    program = tmp_path / "default_mode.chr"
    program.write_text(PROGRAM)
    result = subprocess.run(
        [ychr_bin, str(program)],
        input=":quit\n",
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, f"ychr failed:\n{result.stdout}\n{result.stderr}"
    assert "ychr> " in result.stdout, "default mode should show the prompt"
