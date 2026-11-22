#!/usr/bin/env bash
# Time the MicroHs build of ychr against the GHC build.
#
# Run it with `make bench-mhs`, which builds both binaries first. Use it
# after a MicroHs bump. See dev-docs/MICROHS_PERFORMANCE.md §9.
#
# Each command runs on both binaries, pinned to one core, alternating
# GHC and MicroHs, ROUNDS times (BIG_ROUNDS for `check typechecker`, which
# takes about 2 minutes on MicroHs). The script checks that both binaries
# print the same thing (stdout and stderr). `check` prints nothing when it
# passes, so for the check_* commands that only says both passed. A
# command that fails stops the script.
#
# Results go to $OUT_DIR/<date>-<commit>/ (default bench-results/mhs, which
# is gitignored):
#   results.tsv  one line per run
#   summary.md   medians and ratios
#   out/         what each command printed
#
# Columns of results.tsv:
#   name impl round wall_s mhs_expired_s mhs_reductions mhs_gc_s load1
# The mhs_* columns come from the MicroHs runtime (+RTS -v); reductions
# are the same in every round. load1 is the 1-minute load average before
# the run. It includes the script's own previous run, so expect about 1
# after a long one; much more than that means something else was running
# and the round is not worth much.
#
# Usage: tools/bench-mhs.sh [NAME...]   (from the repo root)
# Names: leq fib18 leq_closure search_label sum_list compile_tc check_leq
#        check_pairs check_tc. No names means all of them.
#
# Environment: ROUNDS (3), BIG_ROUNDS (2), CORE (2), OUT_DIR,
# GHC_YCHR (cabal list-bin exe:ychr), MHS_YCHR (dist-mcabal/bin/mhs/ychr).
set -eu
export LC_ALL=C

ROUNDS=${ROUNDS:-3}
BIG_ROUNDS=${BIG_ROUNDS:-2}
CORE=${CORE:-2}
GHC_YCHR=${GHC_YCHR:-$(cabal list-bin exe:ychr)}
MHS_YCHR=${MHS_YCHR:-./dist-mcabal/bin/mhs/ychr}
ALL="leq fib18 leq_closure search_label sum_list compile_tc check_leq check_pairs check_tc"
NAMES=${*:-$ALL}
for name in $NAMES; do
  case " $ALL " in *" $name "*) ;; *) echo "unknown benchmark: $name" >&2; exit 2 ;; esac
done
[ "$ROUNDS" -ge 1 ] && [ "$BIG_ROUNDS" -ge 1 ] || { echo "ROUNDS must be >= 1" >&2; exit 2; }

# Build the args by splitting words (see run_one), so no spaces here.
DIR=${OUT_DIR:-bench-results/mhs}/$(date +%Y-%m-%d-%H%M)-$(git describe --always --dirty)
case $DIR in *[[:space:]]*) echo "OUT_DIR must not contain spaces" >&2; exit 2 ;; esac
mkdir -p "$DIR/out/ghc" "$DIR/out/mhs"
TSV=$DIR/results.tsv

# Arguments for one command. The goals are the ones in test/golden, except
# fib, which uses 18 instead of 10 so it runs long enough to measure.
cmd_args() {
  case $1 in
    leq)          echo "run --no-check --show-bindings -g order:leq(X,X) test/golden/leq/leq.chr" ;;
    fib18)        echo "run --no-check --show-bindings -g fib:fib(18,R) test/golden/fib/fib.chr" ;;
    leq_closure)  echo "run --no-check --show-bindings -g leqc:run(20) test/golden/leq_closure/leq_closure.chr" ;;
    search_label) echo "run --no-check --show-bindings -g search_label(X,Y,Z,Ss) test/golden/search_label/search_label.chr" ;;
    sum_list)     echo "run --no-check --show-bindings -g sum_list_test:go([10,20,3,4],R) test/golden/sum_list_test/sum_list_test.chr" ;;
    compile_tc)   echo "compile --no-check -t vm -d $DIR/out/$2 typechecker/*.chr" ;;
    check_leq)    echo "check test/golden/leq/leq.chr" ;;
    check_pairs)  echo "check test/golden/pairs_library/pairs_library.chr" ;;
    check_tc)     echo "check typechecker/*.chr" ;;
  esac
}

now() { date +%s.%N; }
elapsed() { awk -v s="$1" -v e="$2" 'BEGIN {printf "%.3f", e - s}'; }

# Run a command; on failure say where its output is and stop.
run_or_die() {
  "$@" >"$out.stdout" 2>"$out.stderr" || {
    echo "FAIL: $name on $impl, see $out.stdout and $out.stderr" >&2
    exit 1
  }
}

# Run one command on one binary and append a line to results.tsv.
# The words of $args are split on purpose, and typechecker/*.chr expands
# here. Other words with glob characters ([10,20,3,4]) only expand if a
# file matches them, which none does.
run_one() {
  name=$1 impl=$2 round=$3
  args=$(cmd_args "$name" "$impl")
  out=$DIR/out/$name.$impl
  load=$(cut -d' ' -f1 /proc/loadavg)
  if [ "$impl" = ghc ]; then
    s=$(now)
    # shellcheck disable=SC2086
    run_or_die taskset -c "$CORE" "$GHC_YCHR" $args
    e=$(now)
    exp=- red=- gc=-
  else
    s=$(now)
    # shellcheck disable=SC2086
    run_or_die taskset -c "$CORE" "$MHS_YCHR" $args +RTS -v -RTS
    e=$(now)
    # +RTS -v prints its counters to stdout, after the program's output.
    exp=$(awk '/total expired/ {sub("s", "", $1); print $1}' "$out.stdout")
    red=$(awk '/ reductions \(/ {gsub(",", "", $1); print $1}' "$out.stdout")
    gc=$(awk '/gc expired/ {sub("s", "", $1); print $1}' "$out.stdout")
    sed -i '/combinator file size/,$d' "$out.stdout"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$impl" "$round" "$(elapsed "$s" "$e")" "$exp" "$red" "$gc" "$load" \
    | tee -a "$TSV"
}

# The two binaries should print the same thing. MicroHs writes the paths
# of the embedded libraries with a leading ./, so drop that before
# comparing the compiled VM. `compile` prints only the path it wrote.
check_same() {
  name=$1
  if [ "$name" = compile_tc ]; then
    # stdout is just the output path, which differs; compare the file.
    if ! cmp -s "$DIR/out/ghc/program.vm" \
      <(sed 's|"\./libraries/|"libraries/|g' "$DIR/out/mhs/program.vm"); then
      echo "WARNING: compile_tc: program.vm differs" | tee -a "$DIR/warnings"
    fi
  else
    for f in stdout stderr; do
      if ! cmp -s "$DIR/out/$name.ghc.$f" "$DIR/out/$name.mhs.$f"; then
        echo "WARNING: $name: GHC and MicroHs $f differ" | tee -a "$DIR/warnings"
      fi
    done
  fi
}

{
  echo "commit: $(git describe --always --dirty)"
  echo "date:   $(date -Iseconds)"
  echo "mhs:    $(mhs --version 2>/dev/null | head -1) (the mhs on PATH)"
  echo "ghc:    $(ghc --numeric-version 2>/dev/null)"
  echo "cpu:    $(awk -F': ' '/model name/ {print $2; exit}' /proc/cpuinfo)"
} >"$DIR/info"

for name in $NAMES; do
  n=$ROUNDS
  [ "$name" = check_tc ] && n=$BIG_ROUNDS
  for r in $(seq 1 "$n"); do
    run_one "$name" ghc "$r"
    run_one "$name" mhs "$r"
  done
  check_same "$name"
done

# Medians of the wall clock, and the ratio MicroHs/GHC.
{
  cat "$DIR/info"
  echo
  echo "| command | GHC | MicroHs | ratio | MicroHs GC | reductions |"
  echo "|---|---:|---:|---:|---:|---:|"
  awk -F'\t' '
    function median(s,   a, n, t, i, j) {
      n = split(s, a, " ")
      for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++)
        if (a[j] + 0 < a[i] + 0) { t = a[i]; a[i] = a[j]; a[j] = t }
      return n % 2 ? a[(n + 1) / 2] : (a[n / 2] + a[n / 2 + 1]) / 2
    }
    !seen[$1]++ { order[++k] = $1 }
    { wall[$1, $2] = wall[$1, $2] " " $4 }
    $2 == "mhs" { gc[$1] = gc[$1] " " $7; red[$1] = $6 }
    END {
      for (i = 1; i <= k; i++) {
        c = order[i]; g = median(wall[c, "ghc"]); m = median(wall[c, "mhs"])
        printf "| %s | %.3f s | %.3f s | %.1fx | %.2f s | %s |\n",
          c, g, m, m / g, median(gc[c]), red[c]
      }
    }' "$TSV"
  if [ -f "$DIR/warnings" ]; then echo; cat "$DIR/warnings"; fi
} >"$DIR/summary.md"

echo
cat "$DIR/summary.md"
echo
echo "Results in $DIR"
