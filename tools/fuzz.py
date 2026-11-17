#!/usr/bin/env python3
"""Differential test of sat against z3 on random small CNF formulas.

Usage: fuzz.py SAT Z3 N [SEED]

For each random formula (DIMACS, up to 14 variables, clauses of 0 to 4 literals, the number of
clauses around the satisfiability threshold) both solvers must give the same answer; z3 reads the
same DIMACS text (`z3 -dimacs`). The solver enumerates all assignments, so the formulas are small.
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
    return "\n".join(lines) + "\n"


def answer(cmd, src):
    out = subprocess.run(cmd, input=src, capture_output=True, text=True, timeout=TIMEOUT).stdout
    for w in ("UNSATISFIABLE", "unsat", "SATISFIABLE", "sat"):
        if w in out.split():
            return w.lower().replace("isfiable", "")
    return "error: " + out.strip()[:200]


def main():
    binary, z3, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    counts = {"sat": 0, "unsat": 0}
    for i in range(n):
        src = gen()
        a = answer([binary], src)
        b = answer([z3, "-dimacs", "-in"], src)
        if a != b or a not in counts:
            print("MISMATCH on formula %d: sat says %s, z3 says %s\n%s" % (i, a, b, src))
            sys.exit(1)
        counts[a] += 1
    print("ok: %d formulas, %d sat, %d unsat" % (n, counts["sat"], counts["unsat"]))


if __name__ == "__main__":
    main()
