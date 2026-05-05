"""Verify that every relative markdown link in the repository's
markdown files points to an existing file.

Each markdown file is parametrized as its own test case. The harness:

- Walks every ``*.md`` file under the repository root, skipping hidden
  directories (``.git``, ``.claude*``, ...) and build output
  (``dist-newstyle``, ``__pycache__``).
- Strips fenced and inline code spans before extracting links, so URLs
  inside code blocks are not validated.
- Skips link targets that are absolute URLs (``http:``, ``https:``,
  ``mailto:``, ...) or pure intra-page anchors (``#section``).
- For ``path#anchor`` links, only the file part is checked.
- Resolves the remaining link targets relative to the directory of the
  containing markdown file and asserts the resulting path exists.
"""

import os
import re
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[2]

# Directory names skipped during the markdown walk.
SKIP_DIRS = {
    "dist-newstyle",
    "__pycache__",
}

# Matches a markdown link of the form [text](target). Targets cannot
# contain a literal ')' — that is fine for our docs.
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

# Matches things that look like URL schemes (e.g. http:, mailto:).
SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.\-]*:")


def find_markdown_files():
    files = []
    for root, dirs, filenames in os.walk(PROJECT_ROOT):
        dirs[:] = [
            d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")
        ]
        for name in filenames:
            if name.endswith(".md"):
                files.append(Path(root) / name)
    return sorted(files)


def extract_links(text):
    # Drop fenced code blocks, then inline code spans, before scanning
    # for links — examples in code blocks are illustrative, not
    # navigational.
    cleaned = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
    cleaned = re.sub(r"`[^`\n]*`", "", cleaned)
    return LINK_RE.findall(cleaned)


@pytest.mark.parametrize(
    "md_file",
    find_markdown_files(),
    ids=lambda p: str(p.relative_to(PROJECT_ROOT)),
)
def test_links_resolve(md_file):
    text = md_file.read_text(encoding="utf-8")
    broken = []
    for raw in extract_links(text):
        target = raw.strip()
        if not target or target.startswith("#"):
            continue
        if SCHEME_RE.match(target):
            continue
        path_part = target.split("#", 1)[0]
        if not path_part:
            continue
        resolved = (md_file.parent / path_part).resolve()
        if not resolved.exists():
            broken.append((target, str(resolved)))
    assert not broken, (
        f"Broken links in {md_file.relative_to(PROJECT_ROOT)}:\n"
        + "\n".join(f"  {t} -> {r}" for t, r in broken)
    )
