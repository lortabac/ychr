"""Shared fixtures for Scheme backend golden tests."""

import os
import shutil
import subprocess

import pytest

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


@pytest.fixture(scope="session")
def project_root():
    return PROJECT_ROOT


@pytest.fixture(scope="session")
def scheme_lib_dir():
    return os.path.join(PROJECT_ROOT, "scheme")


@pytest.fixture(scope="session")
def ychr_bin():
    """Build and return the path to the ychr binary."""
    result = subprocess.run(
        ["cabal", "list-bin", "ychr"],
        capture_output=True,
        text=True,
        cwd=PROJECT_ROOT,
    )
    if result.returncode != 0:
        pytest.fail(f"cabal list-bin failed: {result.stderr}")
    return result.stdout.strip()


@pytest.fixture(scope="session")
def guile_bin():
    """Return the guile3.0 binary path, or skip if not available."""
    path = shutil.which("guile3.0")
    if path is None:
        pytest.skip("guile3.0 not found")
    return path
