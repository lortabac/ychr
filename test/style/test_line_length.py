"""Enforce the line-length rule from ``dev-docs/STYLE.md``.

The style guide asks authors to keep Haskell source lines at roughly 90
characters or fewer. ``ormolu`` does not enforce a hard limit, so this
test acts as the backstop: it fails if any tracked Haskell file has a
line longer than ``MAX_LINE_LENGTH`` characters.

Each Haskell file is parametrized as its own test case so failures
point directly at the offending file. The reported line numbers list
every violation in that file in one shot.
"""

import os
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[2]

# Roots under which Haskell sources are checked.
SOURCE_ROOTS = ("src", "test", "app", "bench")

# Hard limit. The style guide phrases the rule as "roughly 90
# characters"; the test allows a small margin so authors are not nagged
# about lines that are only a character or two over.
MAX_LINE_LENGTH = 95


def find_haskell_files():
    files = []
    for root in SOURCE_ROOTS:
        root_path = PROJECT_ROOT / root
        if not root_path.exists():
            continue
        for dirpath, _dirnames, filenames in os.walk(root_path):
            for name in filenames:
                if name.endswith(".hs"):
                    files.append(Path(dirpath) / name)
    return sorted(files)


@pytest.mark.parametrize(
    "hs_file",
    find_haskell_files(),
    ids=lambda p: str(p.relative_to(PROJECT_ROOT)),
)
def test_line_length(hs_file):
    violations = []
    with hs_file.open(encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):
            stripped = line.rstrip("\n").rstrip("\r")
            if len(stripped) > MAX_LINE_LENGTH:
                violations.append((lineno, len(stripped)))
    assert not violations, (
        f"{hs_file.relative_to(PROJECT_ROOT)} has lines longer than "
        f"{MAX_LINE_LENGTH} characters:\n"
        + "\n".join(f"  line {n}: {ln} chars" for n, ln in violations)
    )
