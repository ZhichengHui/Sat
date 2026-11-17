#!/usr/bin/env bash
# Usage: tools/check.sh [MINUTES]
# Checks every proof of this project: the sources (urust/, spec/, proof/) are copied to a task
# directory on the checking machine, which also gets a ROOTS file listing them and a ROOT with one
# session named after the task that imports the top-level theorem (and with it every theory of the
# project). `isabelle build` (without -b, so no heap is kept) runs as a transient systemd unit
# limited to MINUTES minutes (default 120) and 16 GB, on top of the AutoCorrode heap of the
# Isabelle user directory there. Prints the sessions built, Isabelle's errors and the exit code;
# the log stays in the task directory. The task directory and the unit are named after the
# checkout's directory, so checks of different worktrees can run at the same time.
#
# Configuration (machine-specific, not in this repository): the environment, or the file
# $SOLVER_ENV (default ~/.config/verified-solvers.env), sets
#   CHECK_HOST          ssh destination of the checking machine (unset or empty: this machine)
#   CHECK_WORK          directory on the checking machine for the task directories
#   ISABELLE            the isabelle executable on the checking machine
#   ISABELLE_USER_HOME  HOME for Isabelle there (its user directory holds the AutoCorrode heap)
set -euo pipefail
M=${1:-120}
ENVF=${SOLVER_ENV:-$HOME/.config/verified-solvers.env}
if [ -f "$ENVF" ]; then . "$ENVF"; fi
: "${CHECK_WORK:?not set: see the header of tools/check.sh}"
: "${ISABELLE:?not set: see the header of tools/check.sh}"
: "${ISABELLE_USER_HOME:?not set: see the header of tools/check.sh}"
HERE=$(cd "$(dirname "$0")/.." && pwd)
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1)
P=$(echo "$NAME" | tr '[:upper:]' '[:lower:]')
SESSIONS=$(cat "$HERE/urust/ROOT" "$HERE/spec/ROOT" "$HERE/proof/ROOT" | sed -n 's/^session "\([A-Za-z0-9_]*\)".*/"\1"/p' | tr '\n' ' ')
TAG=$(basename "$HERE" | tr -c 'A-Za-z0-9\n' '-' | tr '[:upper:]' '[:lower:]')
W=$CHECK_WORK/$P-check-$TAG
U=${NAME}Check_Task
if [ -n "${CHECK_HOST:-}" ]; then
  RUN=(ssh -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=40 "$CHECK_HOST")
else
  RUN=(bash -c)
fi
tar -C "$HERE" -czf - urust spec proof | "${RUN[@]}" "
  set -e; mkdir -p $W && cd $W && rm -rf urust spec proof check && tar -xzf - && mkdir -p check
  printf 'urust\nspec\nproof\n' > ROOTS
  printf 'session \"$U\" in \"check\" = \"AutoCorrode\" +\n  options [document = false]\n  sessions\n    $SESSIONS\n  theories\n    \"${NAME}_Top.${NAME}_Top\"\n' > ROOT
  rm -f check.log
  systemd-run --user --unit=${P}-check-$TAG --collect -p RuntimeMaxSec=$((M * 60)) -p MemoryMax=16G \
    bash -c 'HOME=$ISABELLE_USER_HOME $ISABELLE build -v -o threads=4 -d $W $U > $W/check.log 2>&1; echo EXIT \$? >> $W/check.log' > /dev/null 2>&1
  while systemctl --user is-active --quiet ${P}-check-$TAG; do sleep 30; done
  grep -E '^(Building|Finished|Unfinished|\*\*\*|EXIT)' check.log | head -60" 2>&1 \
  | grep --line-buffered -v -i "post-quantum\|store now\|upgraded\|pq.html"
