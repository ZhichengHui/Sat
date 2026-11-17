#!/usr/bin/env bash
# Usage: bench/run.sh SUITE [JOBS]
# Runs the release build of the solver (`cargo build --release` first) on the benchmark suite
# bench/SUITE, JOBS instances at a time (default: the number of processors), and checks every
# answer against the known one (and, where the suite can, every model).
#
# A suite is a directory bench/SUITE with one file, suite.sh, which sets
#   DESCRIPTION   what the suite measures
#   TIMEOUT       seconds per instance
#   MEMORY_MB     memory per instance
# and defines `fetch DIR`, which puts the instances in DIR and, in DIR/expected, one line
# `FILE sat|unsat` per instance; it may also define `check_model FILE OUTPUT` (exit 0 when the
# solver's output OUTPUT holds a model of FILE). To add a suite, add such a directory.
#
# Writes bench/out/SUITE-<commit>.csv (instance,expected,answer,seconds,result with result one of
# ok, wrong, timeout, error) and prints a summary: solved, wrong, timeout, error, PAR-2. Exits 1 if
# any answer is wrong. bench/out/ (instances and results) is not committed.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SUITE=${1:?usage: bench/run.sh SUITE [JOBS]}; JOBS=${2:-$(nproc)}
[ -f "$HERE/bench/$SUITE/suite.sh" ] || { echo "no suite bench/$SUITE" >&2; exit 2; }
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1 | tr '[:upper:]' '[:lower:]')
export BIN=${BIN:-$HERE/target/release/$NAME}
[ -x "$BIN" ] || { echo "no solver $BIN: run cargo build --release" >&2; exit 2; }
export SUITE_SH=$HERE/bench/$SUITE/suite.sh
. "$SUITE_SH"
OUT=$HERE/bench/out; INST=$OUT/instances/$SUITE; mkdir -p "$OUT"
if [ ! -f "$INST/expected" ]; then rm -rf "$INST"; mkdir -p "$INST"; fetch "$INST"; fi
REV=$(git -C "$HERE" rev-parse --short HEAD)$(git -C "$HERE" diff --quiet HEAD -- . ':!bench/out' || echo "-dirty")
CSV=$OUT/$SUITE-$REV.csv
export TIMEOUT MEMORY_MB INST
one() {   # one instance: prints a CSV line
  f=$1; exp=$2; . "$SUITE_SH"; o=$(mktemp)
  t0=$(date +%s.%N)
  ( ulimit -v $((MEMORY_MB * 1024)); timeout "$TIMEOUT" "$BIN" "$INST/$f" > "$o" 2>/dev/null ) && rc=0 || rc=$?
  t=$(echo "$(date +%s.%N) - $t0" | bc)
  ans=$(awk 'NR==1{a=$NF} END{print tolower(a)}' "$o"); ans=${ans/satisfiable/sat}; ans=${ans/unsat/unsat}
  case "$ans" in sat|unsat) ;; *) ans=none ;; esac
  if [ $rc = 124 ]; then r=timeout; ans=none
  elif [ "$ans" = none ]; then r=error
  elif [ "$ans" != "$exp" ]; then r=wrong
  elif [ "$ans" = sat ] && declare -F check_model > /dev/null && ! check_model "$INST/$f" "$o"; then r=wrong
  else r=ok; fi
  rm -f "$o"; echo "$f,$exp,$ans,$t,$r"
}
export -f one
{ echo "instance,expected,answer,seconds,result"
  xargs -P "$JOBS" -L 1 bash -c 'one "$0" "$1"' < "$INST/expected" | sort; } > "$CSV"
echo "$SUITE ($DESCRIPTION) at $REV, timeout ${TIMEOUT}s:"
awk -F, -v T="$TIMEOUT" 'NR>1{n++; c[$5]++; s += ($5=="ok") ? $4 : 2*T}
  END{printf "  %d instances: %d solved, %d wrong, %d timeout, %d error; PAR-2 %.2f s\n",
      n, c["ok"], c["wrong"], c["timeout"], c["error"], s/n}' "$CSV"
echo "  details: ${CSV#$HERE/}"
! grep -q ',wrong$' "$CSV"
