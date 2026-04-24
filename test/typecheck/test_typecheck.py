"""Verify that the type checker CHR program itself is well-typed."""

import os


def test_typecheck_typechecker(ychr_bin, project_root):
    import subprocess

    program = os.path.join(project_root, "typechecker", "typechecker.chr")
    result = subprocess.run(
        [ychr_bin, "check", program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"type check failed:\n{result.stderr}"
