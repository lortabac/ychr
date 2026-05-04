#!/usr/bin/env bash
# One-shot migration: move golden tests from the flat
#   test/golden/{programs,goals,expected}/<name>.{chr,goal,expected,error}
# layout into the per-test-directory layout
#   test/golden/<name>/<name>.{chr,goal,expected,error}
#
# Idempotent: if test/golden/programs no longer exists, exits cleanly.
# History-preserving: uses `git mv` for every move.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

if [ ! -d test/golden/programs ]; then
  echo "Old layout already removed; nothing to do."
  exit 0
fi

cd test/golden

for chr in programs/*.chr; do
  name=$(basename "$chr" .chr)
  mkdir -p "$name"
  git mv "programs/$name.chr" "$name/$name.chr"
  if [ -f "expected/$name.expected" ]; then
    git mv "goals/$name.goal" "$name/$name.goal"
    git mv "expected/$name.expected" "$name/$name.expected"
  elif [ -f "expected/$name.error" ]; then
    git mv "expected/$name.error" "$name/$name.error"
    # Negative-test .goal content is unused; drop it.
    git rm "goals/$name.goal"
  else
    echo "ERROR: $name has neither .expected nor .error" >&2
    exit 1
  fi
done

rmdir programs goals expected 2>/dev/null || true
echo "Migration complete."
