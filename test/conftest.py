"""Shared fixtures for all test suites."""

import os
import subprocess

import pytest

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


@pytest.fixture(scope="session")
def project_root():
    return PROJECT_ROOT


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
def stlc_bin():
    """Return the path to the stlc-typechecker example binary."""
    result = subprocess.run(
        ["cabal", "list-bin", "stlc-typechecker"],
        capture_output=True,
        text=True,
        cwd=PROJECT_ROOT,
    )
    if result.returncode != 0:
        pytest.fail(f"cabal list-bin failed: {result.stderr}")
    return result.stdout.strip()


@pytest.fixture(scope="session")
def playground_bin():
    """Return the path to the web playground's native harness.

    The harness (``playground/Main.hs``) drives ``YCHR.Playground``, the
    same engine the WASM module wraps, over a command protocol — so it
    tests the bridge without emscripten.
    """
    result = subprocess.run(
        ["cabal", "list-bin", "ychr-playground"],
        capture_output=True,
        text=True,
        cwd=PROJECT_ROOT,
    )
    if result.returncode != 0:
        pytest.fail(f"cabal list-bin failed: {result.stderr}")
    return result.stdout.strip()
