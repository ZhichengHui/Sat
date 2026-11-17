#!/usr/bin/env bash
# Usage: tools/check-spec.sh            check spec/ (CI runs this)
#        tools/check-spec.sh --update   rewrite the manifest tools/spec.sha256 (the owner only)
#
# The rule it enforces (see PLAN.md): spec/ is fixed, with one exception. The locale <NAME>_heap in
# spec/<NAME>_Spec.thy repeats the generated locale <NAME>_ctx of urust/<NAME>_Locale.thy without its
# fuel line, and changes with it when the implementation uses a new type of mutable local.
#   1. Every file of spec/, with the locale <NAME>_heap cut out, has the hash recorded in
#      tools/spec.sha256, and spec/ has exactly the files listed there.
#   2. The locale <NAME>_heap is the generated <NAME>_ctx with "_ctx" renamed "_heap" and without
#      the line "+ fixes urust_fuel :: nat".
# <NAME> is the session name in urust/ROOT.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
NAME=$(sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' urust/ROOT | head -1)
SPEC=spec/${NAME}_Spec.thy
MANIFEST=tools/spec.sha256

# The lines of a file without the locale <NAME>_heap (from "locale <NAME>_heap =" up to the line
# before the next "begin").
cut_locale() {
  awk -v start="locale ${NAME}_heap =" '
    $0 == start { skip = 1 }
    skip && $0 == "begin" { skip = 0 }
    !skip { print }' "$1"
}

# The locale <NAME>_heap of the spec, and the one expected from the generated locale.
spec_locale() {
  awk -v start="locale ${NAME}_heap =" '
    $0 == start { on = 1 }
    on && $0 == "begin" { exit }
    on { print }' "$SPEC"
}
expected_locale() {
  awk -v start="locale ${NAME}_ctx =" '
    $0 == start { on = 1 }
    on && $0 ~ /^  \+ fixes urust_fuel :: nat$/ { exit }
    on { print }' "urust/${NAME}_Locale.thy" | sed "1s/locale ${NAME}_ctx =/locale ${NAME}_heap =/"
}

hashes() {
  find spec -type f | LC_ALL=C sort | while read -r f; do
    printf '%s  %s\n' "$(cut_locale "$f" | sha256sum | cut -d' ' -f1)" "$f"
  done
}

if [ "${1:-}" = --update ]; then
  hashes > "$MANIFEST"
  echo "wrote $MANIFEST"
  exit 0
fi

status=0
if ! diff <(hashes) <(LC_ALL=C sort -k2 "$MANIFEST") > /dev/null; then
  echo "spec/ differs from $MANIFEST outside the locale ${NAME}_heap:"
  diff <(hashes) <(LC_ALL=C sort -k2 "$MANIFEST") || true
  status=1
fi
if [ -z "$(spec_locale)" ]; then
  echo "no locale ${NAME}_heap in $SPEC"
  status=1
elif ! diff <(spec_locale) <(expected_locale) > /dev/null; then
  echo "the locale ${NAME}_heap in $SPEC is not the generated ${NAME}_ctx without its fuel line:"
  diff <(spec_locale) <(expected_locale) || true
  status=1
fi
[ $status = 0 ] && echo "spec/ ok: unchanged outside the locale ${NAME}_heap, which matches urust/${NAME}_Locale.thy"
exit $status
