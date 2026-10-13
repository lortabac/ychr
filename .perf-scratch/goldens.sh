#!/usr/bin/env bash
# Run every positive golden case in the given directories on the Scheme
# backend and report mismatches. Not part of the repo: a scratch harness.
set -u
WT=/home/lorenzo/Development/ychr/.worktrees/search-scheme-2
YCHR_BIN=$WT/dist-newstyle1/build/x86_64-linux/ghc-9.14.1/ychr-0.1.0.0/x/ychr/build/ychr/ychr
cd "$WT" || exit 1
pass=0; fail=0; failed=""
for dir in "$@"; do
  [ -d "test/golden/$dir" ] || continue
  rm -rf ".perf-scratch/run-$dir"; mkdir -p ".perf-scratch/run-$dir"
  if ! "$YCHR_BIN" compile -t scheme -d ".perf-scratch/run-$dir" "test/golden/$dir"/*.chr >/dev/null 2>&1; then
    echo "COMPILE FAIL $dir"; fail=$((fail+1)); failed="$failed $dir(compile)"; continue
  fi
  for goal in "test/golden/$dir"/*.goal; do
    base="${goal%.goal}"; name="$(basename "$base")"
    exp="$base.expected"
    [ -f "$exp" ] || continue
    if ! "$YCHR_BIN" gen-driver -g "$(cat "$goal")" "test/golden/$dir"/*.chr > ".perf-scratch/run-$dir/d.sps" 2>/dev/null; then
      echo "DRIVER FAIL $dir/$name"; fail=$((fail+1)); failed="$failed $dir/$name(driver)"; continue
    fi
    out=$(GUILE_AUTO_COMPILE=0 timeout 60 guile3.0 --r6rs --no-auto-compile \
          -L scheme -L ".perf-scratch/run-$dir" ".perf-scratch/run-$dir/d.sps" 2>&1)
    if [ "$out" = "$(cat "$exp")" ]; then
      pass=$((pass+1))
    else
      fail=$((fail+1)); failed="$failed $dir/$name"
      if [ "${VERBOSE:-0}" = "1" ]; then
        echo "FAIL $dir/$name"
        echo "  got: $(echo "$out" | tr '\n' '|')"
        echo "  exp: $(cat "$exp" | tr '\n' '|')"
      fi
    fi
  done
done
echo "pass=$pass fail=$fail"
[ -n "$failed" ] && echo "failed:$failed"
exit 0
