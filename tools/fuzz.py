#!/usr/bin/env python3
"""Differential test of sat against z3 on random small CNF formulas.

Usage: fuzz.py SAT Z3 N [SEED]

For each random formula (DIMACS, up to 14 variables, clauses of 0 to 4 literals, the number of
clauses around the satisfiability threshold) both solvers must give the same answer; z3 reads the
same DIMACS text (`z3 -dimacs`). Every satisfiable answer of the solver must come with `v` lines
that give each variable one value, end with `0`, and satisfy every clause. The solver enumerates
all assignments, so the formulas are small.
The last line of the output is `ok: ...` when every answer agrees.
"""
import random
import subprocess
import sys

TIMEOUT = 60


def gen():
    n = random.randint(0, 14)
    m = random.randint(0, 5 * n + 2)
    cs = []
    for _ in range(m):
        k = random.choice([0] + [1] * 2 + [2] * 4 + [3] * 12 + [4] * 4) if n else 0
        cs.append([random.randint(1, n) * random.choice([1, -1]) for _ in range(k)])
    lines = ["p cnf %d %d" % (n, len(cs))] + [" ".join(map(str, c + [0])) for c in cs]
    return n, cs, "\n".join(lines) + "\n"


def model_error(n, cs, out):
    """None if the v lines of `out` are a model of the clauses `cs` over n variables, else why not."""
    lits = []
    for line in out.splitlines():
        if line.startswith("v"):
            lits += [int(t) for t in line.split()[1:]]
    if not lits or lits[-1] != 0:
        return "the v lines do not end with 0"
    value = {}
    for x in lits[:-1]:
        if x == 0 or abs(x) > n or abs(x) in value:
            return "bad or repeated literal %d" % x
        value[abs(x)] = x > 0
    if len(value) != n:
        return "not every variable has a value"
    for c in cs:
        if not any(value[abs(x)] == (x > 0) for x in c):
            return "clause %s is false" % c
    return None


def answer(cmd, src):
    out = subprocess.run(cmd, input=src, capture_output=True, text=True, timeout=TIMEOUT).stdout
    for w in ("UNSATISFIABLE", "unsat", "SATISFIABLE", "sat"):
        if w in out.split():
            return w.lower().replace("isfiable", ""), out
    return "error: " + out.strip()[:200], out


def main():
    binary, z3, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    counts = {"sat": 0, "unsat": 0}
    for i in range(n):
        nv, cs, src = gen()
        a, out = answer([binary], src)
        b, _ = answer([z3, "-dimacs", "-in"], src)
        if a != b or a not in counts:
            print("MISMATCH on formula %d: sat says %s, z3 says %s\n%s" % (i, a, b, src))
            sys.exit(1)
        err = model_error(nv, cs, out) if a == "sat" else None
        if err:
            print("BAD MODEL on formula %d: %s\n%s\n%s" % (i, err, src, out))
            sys.exit(1)
        counts[a] += 1
    print("ok: %d formulas, %d sat, %d unsat" % (n, counts["sat"], counts["unsat"]))


if __name__ == "__main__":
    main()
