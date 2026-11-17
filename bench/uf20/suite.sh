# The minimal suite: SATLIB uniform random 3-SAT with 20 variables and 91 clauses (uf20-91),
# the first 100 of its 1000 instances (by name), all satisfiable. Every model is checked.
DESCRIPTION="SATLIB uf20-91, 100 satisfiable random 3-SAT formulas"
TIMEOUT=10
MEMORY_MB=1024
fetch() {
  local a=$1/uf20-91.tar.gz
  curl -sfL https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf20-91.tar.gz -o "$a"
  echo "be2835295e8500bb28f0314eba70bd0deaff1250b187260f7b6d0772bdf111a5  $a" | sha256sum -c --quiet
  tar -xzf "$a" -C "$1" && rm "$a"
  (cd "$1" && ls uf20-*.cnf | sort -V | head -100 | sed 's/$/ sat/' > expected)
}
check_model() { python3 "$(dirname "$SUITE_SH")/../check_cnf.py" "$1" "$2"; }
