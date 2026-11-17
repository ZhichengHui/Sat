#!/usr/bin/env bash
# Usage: tools/pages-index.sh HTML_DIR [TITLE]
# Gives the HTML that `isabelle build -o browser_info -P HTML_DIR` wrote a front page with this
# project's own sessions: the generated translation (urust/), the specification (spec/) and the
# proofs (proof/), each linking to its session page. Isabelle's library index, which lists every
# chapter of the distribution, stays available as library.html.
set -euo pipefail
OUT=$1
HERE=$(cd "$(dirname "$0")/.." && pwd)
TITLE=${2:-$(basename "$HERE")}
sessions() { sed -n 's/^session "\([A-Za-z0-9_]*\)".*/\1/p' "$HERE/$1/ROOT"; }
item() { echo "<li><a href=\"Unsorted/$1/index.html\">$1</a></li>"; }
[ -f "$OUT/library.html" ] || mv "$OUT/index.html" "$OUT/library.html"
{
  echo '<!DOCTYPE html>'
  echo "<html><head><meta charset=\"utf-8\"/><link rel=\"stylesheet\" type=\"text/css\" href=\"isabelle.css\"/><title>$TITLE</title></head><body>"
  echo "<div class=\"head\"><h1>$TITLE</h1></div>"
  echo '<h2>Specification</h2><ul>'; for s in $(sessions spec); do item "$s"; done; echo '</ul>'
  echo '<h2>Proofs</h2><ul>'; for s in $(sessions proof); do item "$s"; done; echo '</ul>'
  echo '<h2>Translation of the Rust code</h2><ul>'; for s in $(sessions urust); do item "$s"; done; echo '</ul>'
  echo '<p><a href="library.html">Isabelle library index</a></p>'
  echo '</body></html>'
} > "$OUT/index.html"
