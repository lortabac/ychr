"""Fixtures for Scheme backend golden tests."""

import os
import shutil

import pytest

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


@pytest.fixture(scope="session")
def scheme_lib_dir():
    return os.path.join(PROJECT_ROOT, "scheme")


@pytest.fixture(scope="session")
def guile_bin():
    """Return the guile3.0 binary path, or skip if not available."""
    path = shutil.which("guile3.0")
    if path is None:
        pytest.skip("guile3.0 not found")
    return path
