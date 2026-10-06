"""Fixtures for Scheme backend golden tests."""

import os
import shutil
import subprocess

import pytest

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


class CompileCache:
    """Compile a golden directory's ``.chr`` files once per session.

    The harness compiles the same file set for every case in a directory
    (a directory may hold dozens of ``.goal`` files), so the emitted
    library is identical each time. Compiling once and replaying the
    result — including a failure, which every case in the directory must
    then report — removes that repeated work without changing what any
    case asserts.

    Entries are keyed by directory: the ``.chr`` files and the
    ``--Werror`` flag are derived from it, and ``discover_cases`` never
    attributes one directory's cases to another.
    """

    def __init__(self, root):
        self._root = root
        self._entries = {}

    def compile(self, test_dir, chr_files, werror_flags, ychr_bin, cwd):
        """Return ``(library_dir, completed_process)`` for ``test_dir``."""
        entry = self._entries.get(test_dir)
        if entry is None:
            out_dir = self._root / f"{len(self._entries):03d}-{test_dir}"
            out_dir.mkdir()
            result = subprocess.run(
                [
                    ychr_bin,
                    "compile",
                    *werror_flags,
                    "-t",
                    "scheme",
                    "-d",
                    str(out_dir),
                    *chr_files,
                ],
                capture_output=True,
                text=True,
                cwd=cwd,
            )
            entry = self._entries[test_dir] = (out_dir, result)
        return entry


@pytest.fixture(scope="session")
def scheme_compile_cache(tmp_path_factory):
    """A per-session cache of compiled golden libraries.

    ``tmp_path_factory`` is session-scoped (and per pytest-xdist worker),
    so the directory lives for the run and is cleaned up afterwards.
    """
    return CompileCache(tmp_path_factory.mktemp("scheme-compile"))


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
