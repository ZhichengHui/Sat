#!/usr/bin/env python3
"""Checks a model: check-model.py CNF OUT exits 0 iff the `v` lines of the solver output OUT give
every variable of the DIMACS formula CNF one value, end with 0, and satisfy every clause.
A `%` line ends the formula (as in SATLIB files)."""
import sys


def clauses(path):
    n, cs, cur = None, [], []
    with open(path) as f:
        for line in f:
            t = line.strip()
            if t.startswith("%"):
                break
            if not t or t.startswith("c"):
                continue
            if t.startswith("p"):
                n = int(t.split()[2])
                continue
            for x in map(int, t.split()):
                if x == 0:
                    cs.append(cur)
                    cur = []
                else:
                    cur.append(x)
    if cur:
        cs.append(cur)
    return n, cs


def error(cnf, out):
    n, cs = clauses(cnf)
    lits = []
    with open(out) as f:
        for line in f:
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


if __name__ == "__main__":
    e = error(sys.argv[1], sys.argv[2])
    if e:
        print("bad model:", e, file=sys.stderr)
    sys.exit(1 if e else 0)
