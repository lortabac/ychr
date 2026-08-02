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
    """Return the Guile 3 binary path, or skip if not available.

    Honors the GUILE environment variable first, then falls back to the
    common binary names (guile3.0 on Fedora, guile-3.0 on Debian/Ubuntu).
    """
    override = os.environ.get("GUILE")
    if override:
        path = shutil.which(override)
        if path is None:
            pytest.fail(f"GUILE={override} set but not found on PATH")
        return path
    for candidate in ("guile3.0", "guile-3.0", "guile"):
        path = shutil.which(candidate)
        if path is not None:
            return path
    pytest.skip("no Guile 3 binary found (tried guile3.0, guile-3.0, guile)")
