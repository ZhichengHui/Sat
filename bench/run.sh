#!/usr/bin/env bash
# Runs the benchmark suite bench/SUITE (PLAN.md, Benchmarks) on the release build.
#
# Usage: bench/run.sh SUITE [REGEX]
#   REGEX     run only the instances whose name matches it (grep -E)
# Environment:
#   SAT       the solver to run (default target/release/sat; build it with cargo build --release)
#   BENCH_CACHE  where archives and instances are kept (default target/bench-cache)
#   BENCH_TIME_LIMIT  overrides the suite's time limit; results with it are not comparable
#
# bench/SUITE/suite.sh defines TIME_LIMIT (seconds), MEMORY_LIMIT (KiB), ARCHIVES (lines
# `ARCHIVE URL SHA256`) and INSTANCES (lines `ARCHIVE MEMBER ANSWER`, ANSWER sat or unsat).
# Archives are fetched once, checked by hash, and the instances extracted from them. Each instance
# runs once under the limits; a satisfiable answer counts only with a model that bench/check-model.py
# accepts. Prints one line per instance and a summary; exits 1 if an answer is wrong.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
suite=${1:?usage: bench/run.sh SUITE [REGEX]}
filter=${2:-}
[ -f "$root/bench/$suite/suite.sh" ] || { echo "no suite bench/$suite" >&2; exit 2; }
# shellcheck source=/dev/null
source "$root/bench/$suite/suite.sh"
TIME_LIMIT=${BENCH_TIME_LIMIT:-$TIME_LIMIT}
sat=${SAT:-$root/target/release/sat}
[ -x "$sat" ] || { echo "no solver $sat (cargo build --release)" >&2; exit 2; }
cache=${BENCH_CACHE:-$root/target/bench-cache}/$suite
mkdir -p "$cache/archives" "$cache/instances" "$cache/out"

# Fetch and check the archives.
declare -A archive_file
while read -r name url hash; do
    [ -n "$name" ] || continue
    f="$cache/archives/$name.tar.gz"
    if ! echo "$hash  $f" | sha256sum -c --status 2>/dev/null; then
        echo "fetching $url" >&2
        curl -sSfL --max-time 300 -o "$f.part" "$url"
        mv "$f.part" "$f"
        echo "$hash  $f" | sha256sum -c --status || { echo "hash mismatch: $url" >&2; exit 2; }
    fi
    archive_file[$name]=$f
done <<< "$ARCHIVES"

now() { date +%s.%N; }
solved=0; total=0; wrong=0; solved_time=0
printf '%-24s %-6s %-8s %8s\n' INSTANCE ANSWER RESULT SECONDS
while read -r archive member answer; do
    [ -n "$archive" ] || continue
    inst=$(basename "$member" .cnf)
    if [ -n "$filter" ] && ! grep -qE -- "$filter" <<< "$inst"; then
        continue
    fi
    cnf="$cache/instances/$inst.cnf"
    [ -s "$cnf" ] || tar xzf "${archive_file[$archive]}" -O "$member" > "$cnf"
    out="$cache/out/$inst.out"
    start=$(now)
    set +e
    ( ulimit -v "$MEMORY_LIMIT"; exec timeout -s KILL "$TIME_LIMIT" "$sat" "$cnf" ) > "$out" 2>&1
    code=$?
    set -e
    secs=$(echo "$(now) - $start" | bc)
    case $code in
        10) if grep -qx 's SATISFIABLE' "$out" && python3 "$root/bench/check-model.py" "$cnf" "$out"
            then result=sat; else result=bad-model; fi ;;
        20) grep -qx 's UNSATISFIABLE' "$out" && result=unsat || result=error ;;
        124|137) result=timeout ;;
        *) result=error ;;
    esac
    total=$((total + 1))
    if [ "$result" = "$answer" ]; then
        solved=$((solved + 1)); solved_time=$(echo "$solved_time + $secs" | bc)
    elif [ "$result" = sat ] || [ "$result" = unsat ] || [ "$result" = bad-model ]; then
        result="WRONG:$result"; wrong=$((wrong + 1))
    fi
    printf '%-24s %-6s %-8s %8.2f\n' "$inst" "$answer" "$result" "$secs"
done <<< "$INSTANCES"

printf 'suite %s: %d of %d solved in %.2f s (limits %s s, %s KiB), %d wrong\n' \
    "$suite" "$solved" "$total" "$solved_time" "$TIME_LIMIT" "$MEMORY_LIMIT" "$wrong"
[ "$wrong" -eq 0 ]
