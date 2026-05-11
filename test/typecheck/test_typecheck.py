"""Verify that the type checker CHR program itself is well-typed."""

import os


def test_typecheck_typechecker(ychr_bin, project_root):
    import subprocess

    program = os.path.join(project_root, "typechecker", "typechecker.chr")
    result = subprocess.run(
        [ychr_bin, "check", "--Werror", program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"type check failed:\n{result.stderr}"


def test_typecheck_stdlib(ychr_bin, project_root):
    import subprocess

    libraries = os.path.join(project_root, "libraries")
    files = [
        os.path.join(libraries, name)
        for name in ("lists.chr", "strings.chr", "meta.chr", "test.chr")
    ]
    result = subprocess.run(
        [ychr_bin, "check", "--Werror", *files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, (
        f"stdlib type check failed:\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )
