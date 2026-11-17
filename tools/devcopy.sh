#!/usr/bin/env bash
# Usage: tools/devcopy.sh
# Writes dev/, a flat copy of every theory of urust/, spec/ and proof/ in which the session-qualified
# imports (`Sat_Spec.Sat_Spec`) are unqualified (`Sat_Spec`), so that the Isabelle Pool Server can
# open any theory of the project on top of the AutoCorrode heap and load the theories it imports
# from the same directory. Edit the theories in their own directories, run this script, then check
# dev/<Theory>.thy with the Pool Server tools; dev/ is not committed.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
rm -rf "$HERE/dev"; mkdir -p "$HERE/dev"
find "$HERE/urust" "$HERE/spec" "$HERE/proof" -name '*.thy' -exec cp {} "$HERE/dev/" \;
# The sessions of this project (from the ROOT files); imports from other sessions stay qualified.
S=$(cat "$HERE/urust/ROOT" "$HERE/spec/ROOT" "$HERE/proof/ROOT" | sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' | paste -sd'|')
sed -i -E "/^ *imports/,/^begin/ s/\"?\\b($S)\\.([A-Za-z0-9_]+)\\b\"?/\\2/g" "$HERE/dev/"*.thy
echo "dev/: $(ls "$HERE/dev" | wc -l) theories"
