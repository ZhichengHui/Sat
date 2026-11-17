#!/usr/bin/env bash
# Usage, on the PGR compute server in the pod clone of this repository ($RT/pod/Sat):
#   tools/pod-remote.sh [POD ARGS...]        e.g. `tools/pod-remote.sh add 2`, `tools/pod-remote.sh status`
# Runs pod (kim-em/pod, installed in $RT/pod-venv) with the environment the agents need: HOME is the
# agents' home $RT/home (Claude Code settings, the Isabelle skills, the Pool Server MCP), the Claude
# subscription token and the GitHub token come from $RT/secrets, and PATH has claude, gh, cargo and z3.
# Without arguments it starts pod's interactive monitor; run it in tmux (`tmux new -s pod-sat`).
set -euo pipefail
. "$HOME/compute-env/bin/env.sh"
cd "$(dirname "$0")/.."
export HOME=$AGENT_HOME DISABLE_AUTOUPDATER=1
CLAUDE_CODE_OAUTH_TOKEN=$(cat "$RT/secrets/claude_token"); export CLAUDE_CODE_OAUTH_TOKEN
GH_TOKEN=$(cat "$RT/secrets/github_sat_token"); export GH_TOKEN
export RUSTUP_HOME=$RT/rust/rustup CARGO_HOME=$RT/rust/cargo
export PATH=$RT/pod-venv/bin:$RT/claude-code/bin:$RT/local/bin:$RT/rust/cargo/bin:$RT/z3venv/bin:$PATH
touch .pod/force-quota   # one account, no quota helper: see [agent.claude] in .pod/config.toml
exec pod "$@"
