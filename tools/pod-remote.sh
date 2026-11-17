#!/usr/bin/env bash
# Usage, on the PGR compute server in the pod clone of this repository ($RT/pod/<repository>):
#   tools/pod-remote.sh [POD ARGS...]        e.g. `tools/pod-remote.sh add 2`, `tools/pod-remote.sh status`
# Runs pod (kim-em/pod, installed in $RT/pod-venv) with the environment the agents need: HOME is the
# agents' home $RT/home (Claude Code settings, the Isabelle skills, the Pool Server MCP), the Claude
# subscription token and the GitHub token come from $RT/secrets, and PATH has claude, gh, cargo and z3.
# Without arguments it starts pod's interactive monitor; run it in tmux (`tmux new -s pod-<repository>`).
# Nothing here reads AFS (its credentials expire, and a tmux server started earlier has none): the
# runtime root RT of the compute server and the agents' home are set directly.
set -euo pipefail
cd "$(dirname "$0")/.."
RT=/disk/scratch/$(id -un)
export RT HOME=$RT/home DISABLE_AUTOUPDATER=1
CLAUDE_CODE_OAUTH_TOKEN=$(cat "$RT/secrets/claude_token"); export CLAUDE_CODE_OAUTH_TOKEN
GH_TOKEN=$(cat "$RT/secrets/github_pod_token"); export GH_TOKEN   # shared by the pods of all repositories
export RUSTUP_HOME=$RT/rust/rustup CARGO_HOME=$RT/rust/cargo
export PATH=$RT/pod-venv/bin:$RT/claude-code/bin:$RT/local/bin:$RT/rust/cargo/bin:$RT/z3venv/bin:$PATH
# One subscription account, no quota helper (see [agent.claude] in .pod/config.toml). pod picks an
# account from ~/.claude/credentials<N>.json by its accountLabel; with isolated_config = false it
# never reads a token from that file, so it holds only the label. The token is the environment's.
[ -f "$HOME/.claude/credentials1.json" ] || (umask 077; echo '{"accountLabel": "pgr-server"}' > "$HOME/.claude/credentials1.json")
touch .pod/force-quota
exec pod "$@"
