#!/usr/bin/env python3
"""Usage: check_cnf.py FORMULA.cnf OUTPUT

Exit 0 when OUTPUT (the solver's output in the format of the SAT competition) holds `v` lines that
give each variable of the DIMACS formula one value, end with 0, and satisfy every clause."""
import sys

def main():
    n, clauses, cur = 0, [], []
    for line in open(sys.argv[1]):
        t = line.split()
        if not t or t[0] in ("c", "%"):
            if t and t[0] == "%":
                break
            continue
        if t[0] == "p":
            n = int(t[2]); continue
        for x in map(int, t):
            if x == 0:
                clauses.append(cur); cur = []
            else:
                cur.append(x)
    if cur:
        clauses.append(cur)
    lits = [int(x) for line in open(sys.argv[2]) if line.startswith("v") for x in line.split()[1:]]
    if not lits or lits[-1] != 0:
        sys.exit(1)
    value = {}
    for x in lits[:-1]:
        if x == 0 or abs(x) > n or abs(x) in value:
            sys.exit(1)
        value[abs(x)] = x > 0
    if len(value) != n or not all(any(value[abs(x)] == (x > 0) for x in c) for c in clauses):
        sys.exit(1)

main()
