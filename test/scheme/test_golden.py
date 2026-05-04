"""Golden tests for the Scheme backend.

Each test directory under test/golden/ contains one or more .chr files
(compiled together) plus one or more <case>.goal/<case>.expected pairs.
For each case, this harness compiles the program to Scheme, generates a
driver script for the case's goal, runs it with guile3.0, and compares
the output against <case>.expected.

Negative tests (directories containing .error files) are skipped — the
Scheme harness only validates positive output.
"""

import glob
import os
import subprocess

import pytest

GOLDEN_DIR = os.path.join(os.path.dirname(__file__), "..", "golden")

# Test directories whose tests exercise Haskell-only meta-programming
# primitives and therefore cannot run on the Scheme backend.
HASKELL_ONLY = {
    "copy_term_fn",
    "read_term_test",
}


def discover_cases():
    """Return sorted list of (test_dir, case_name) for all positive cases."""
    cases = []
    for entry in sorted(os.listdir(GOLDEN_DIR)):
        dir_path = os.path.join(GOLDEN_DIR, entry)
        if not os.path.isdir(dir_path):
            continue
        # Skip negative-test directories.
        if glob.glob(os.path.join(dir_path, "*.error")):
            continue
        for goal in sorted(glob.glob(os.path.join(dir_path, "*.goal"))):
            case_name = os.path.splitext(os.path.basename(goal))[0]
            cases.append((entry, case_name))
    return cases


@pytest.mark.parametrize("test_dir,case_name", discover_cases())
def test_scheme_golden(test_dir, case_name, ychr_bin, guile_bin, scheme_lib_dir, project_root, tmp_path):
    if test_dir in HASKELL_ONLY:
        pytest.skip(f"{test_dir} uses Haskell-only meta primitives")

    dir_path = os.path.join(GOLDEN_DIR, test_dir)
    chr_files = sorted(glob.glob(os.path.join(dir_path, "*.chr")))
    assert chr_files, f"No .chr files in {dir_path}"
    goal_file = os.path.join(dir_path, f"{case_name}.goal")
    expected_file = os.path.join(dir_path, f"{case_name}.expected")

    with open(goal_file) as f:
        query = f.read().strip()
    with open(expected_file) as f:
        expected = f.read()

    # 1. Compile to Scheme
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), *chr_files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"

    # 2. Generate driver
    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", query, *chr_files],
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
