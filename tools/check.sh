#!/usr/bin/env bash
# Usage: tools/check.sh [MINUTES]
# Checks every proof of this project on the compute server, following the standard procedure of
# the compute environment: the sources (urust/, spec/, proof/) are copied to the task directory
# $RT/work/<project>-check/, which also gets a ROOTS file listing them and a ROOT with one session
# named after the task that imports the top-level theorem (and with it every theory of the
# project). `isabelle build` (without -b, so no heap is kept) runs as a transient systemd unit
# limited to MINUTES minutes (default 120) and 96 GB, on top of the shared AutoCorrode heap.
# Prints the sessions built, Isabelle's errors and the exit code; the log stays in the task
# directory. Nothing is registered in the shared ROOTS file.
# On the compute server itself (pod agents) it runs there directly; elsewhere it goes over ssh. The
# task directory and the unit are named after the checkout's directory, so checks of different
# worktrees can run at the same time.
set -euo pipefail
M=${1:-120}
HERE=$(cd "$(dirname "$0")/.." && pwd)
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/urust/ROOT" | head -1)
P=$(echo "$NAME" | tr '[:upper:]' '[:lower:]')
SESSIONS=$(cat "$HERE/urust/ROOT" "$HERE/spec/ROOT" "$HERE/proof/ROOT" | sed -n 's/^session "\([A-Za-z0-9_]*\)".*/"\1"/p' | tr '\n' ' ')
TAG=$(basename "$HERE" | tr -c 'A-Za-z0-9\n' '-' | tr '[:upper:]' '[:lower:]')
RT=/disk/scratch/s2982359
W=$RT/work/$P-check-$TAG
U=${NAME}Check_Task
if [ -d "$RT/isabelle" ]; then RUN=(bash -c); else RUN=(ssh -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=40
     -o "ProxyCommand=ssh -q s2982359@ssh.inf.ed.ac.uk nc -4 s2982359.pgr.inf.ed.ac.uk 22"
     s2982359@s2982359.pgr.inf.ed.ac.uk); fi
tar -C "$HERE" -czf - urust spec proof | "${RUN[@]}" "
  set -e; mkdir -p $W && cd $W && rm -rf urust spec proof check && tar -xzf - && mkdir -p check
  printf 'urust\nspec\nproof\n' > ROOTS
  printf 'session \"$U\" in \"check\" = \"AutoCorrode\" +\n  options [document = false]\n  sessions\n    $SESSIONS\n  theories\n    \"${NAME}_Top.${NAME}_Top\"\n' > ROOT
  rm -f check.log
  systemd-run --user --unit=${P}-check-$TAG --collect -p RuntimeMaxSec=$((M * 60)) -p MemoryMax=96G \
    bash -c 'HOME=$RT/home $RT/isabelle/Isabelle2026/bin/isabelle build -v -o threads=8 -d $W $U > $W/check.log 2>&1; echo EXIT \$? >> $W/check.log' > /dev/null 2>&1
  while systemctl --user is-active --quiet ${P}-check-$TAG; do sleep 30; done
  grep -E '^(Building|Finished|Unfinished|\*\*\*|EXIT)' check.log | head -60" 2>&1 \
  | grep --line-buffered -v -i "post-quantum\|store now\|upgraded\|pq.html"
