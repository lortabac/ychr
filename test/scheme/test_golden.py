"""Golden tests for the Scheme backend.

Each test compiles a CHR program to Scheme, generates a driver script,
runs it with guile3.0, and compares the output against the expected file.
"""

import glob
import os
import subprocess

import pytest

GOLDEN_DIR = os.path.join(os.path.dirname(__file__), "..", "golden")


def discover_tests():
    """Scan test/golden/goals/*.goal and return sorted test names."""
    goals = glob.glob(os.path.join(GOLDEN_DIR, "goals", "*.goal"))
    return sorted(
        os.path.splitext(os.path.basename(g))[0] for g in goals
    )


@pytest.mark.parametrize("test_name", discover_tests())
def test_scheme_golden(test_name, ychr_bin, guile_bin, scheme_lib_dir, project_root, tmp_path):
    program = os.path.join(GOLDEN_DIR, "programs", f"{test_name}.chr")
    query_file = os.path.join(GOLDEN_DIR, "goals", f"{test_name}.goal")
    expected_file = os.path.join(GOLDEN_DIR, "expected", f"{test_name}.expected")

    with open(query_file) as f:
        query = f.read().strip()
    with open(expected_file) as f:
        expected = f.read()

    # 1. Compile to Scheme
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"

    # 2. Generate driver
    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", query, program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"gen-driver failed:\n{result.stdout}\n{result.stderr}"

    driver_path = tmp_path / "driver.sps"
    driver_path.write_text(result.stdout)

    # 3. Run with Guile
    result = subprocess.run(
        [
            guile_bin,
            "--r6rs",
            "--no-auto-compile",
            "-L", scheme_lib_dir,
            "-L", str(tmp_path),
            str(driver_path),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"guile failed:\n{result.stdout}\n{result.stderr}"

    # 4. Compare output
    assert result.stdout == expected
