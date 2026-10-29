"""Top-level CLI parsing tests.

The default mode (no subcommand) takes no flags, so a flag before a
subcommand is a usage error.
"""

import os
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


# A missing input file must be reported as YCHR-50005. One case per
# entry point that reads files from disk. `{}` stands for the missing
# file's path, filled in per case.
MISSING_FILE_COMMANDS = [
    ["check", "{}"],
    ["run", "-g", "go", "{}"],
    ["compile", "{}"],
    ["gen-driver", "-g", "go", "{}"],
    ["repl", "{}"],
    ["{}"],  # bare `ychr FILE`, default mode
]


@pytest.mark.parametrize(
    "args", MISSING_FILE_COMMANDS, ids=lambda a: " ".join(a) or "bare-file"
)
def test_missing_input_file_is_reported_not_thrown(ychr_bin, tmp_path, args):
    missing = tmp_path / "missing.chr"
    result = subprocess.run(
        [ychr_bin, *(a.format(missing) for a in args)],
        input="",
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "YCHR-50005" in result.stdout
    assert str(missing) in result.stdout
    assert "Uncaught exception" not in result.stderr
    assert "Uncaught exception" not in result.stdout


def test_unwritable_output_dir_is_reported_not_thrown(ychr_bin, tmp_path):
    # Point -d at a path nested under a regular file, so no directory of
    # that name could ever exist.
    program = tmp_path / "p.chr"
    program.write_text(PROGRAM)
    blocker = tmp_path / "blocker"
    blocker.write_text("")
    bad_output_dir = blocker / "subdir"
    result = subprocess.run(
        [ychr_bin, "compile", "-d", str(bad_output_dir), str(program)],
        input="",
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "Error: cannot write" in result.stderr
    assert str(bad_output_dir) in result.stderr
    assert "Uncaught exception" not in result.stderr


def test_utf8_source_compiles_under_c_locale(ychr_bin, tmp_path):
    """compileFiles decodes source files as UTF-8 explicitly, not
    through the process locale, so a valid UTF-8 source still compiles
    under `LC_ALL=C` instead of failing with a locale-decode error."""
    program = tmp_path / "utf8.chr"
    program.write_bytes(
        ("% a comment with caffè, naïve, 日本語\n" + PROGRAM).encode(
            "utf-8"
        )
    )
    result = subprocess.run(
        [ychr_bin, "check", str(program)],
        input="",
        capture_output=True,
        text=True,
        env={**os.environ, "LC_ALL": "C"},
    )
    assert result.returncode == 0, f"check failed:\n{result.stdout}\n{result.stderr}"
