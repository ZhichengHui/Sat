# Suite Sat-2026-11-18: small standard instances from SATLIB, graded from what the present solver decides
# to what needs unit propagation, DPLL and clause learning. A state-of-the-art solver decides every
# instance in well under a second (hole9: a few seconds); read by bench/run.sh (PLAN.md, Benchmarks).
#
# Measures: the number of instances decided correctly within the limits, and the time spent on
# them. Families, in order of difficulty for a solver without propagation (n = variables):
#   uf20 (n=20, sat)                      uniform random 3-SAT at the threshold, 91 clauses
#   uf50 / uuf50 (n=50, sat / unsat)      the same, 218 clauses
#   aim-50, aim-100, aim-200 (yes / no)   artificial 3-SAT with one model or none; easy with
#                                         unit propagation, hard without
#   uf75 / uuf75, uf100 / uuf100          random 3-SAT, 325 and 430 clauses; DPLL territory
#   dubois, pret (unsat)                  parity-like formulas, hard for DPLL without learning
#   hole6 .. hole9 (unsat)                pigeon hole; exponential for resolution, the hardest here
# Source: SATLIB, https://www.cs.ubc.ca/~hoos/SATLIB/benchmarks.html (H. Hoos, T. Stuetzle).
# Answers: uf and aim-*-yes are satisfiable by construction, uuf, aim-*-no, dubois, pret and hole
# unsatisfiable; all were confirmed with z3 when the suite was built.

TIME_LIMIT=20           # seconds of wall-clock time per instance
MEMORY_LIMIT=2097152    # KiB of virtual memory per instance (ulimit -v), 2 GiB

# ARCHIVE URL SHA256: the archives of SATLIB the instances come from, checked by hash.
ARCHIVES='
uf20      https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf20-91.tar.gz     be2835295e8500bb28f0314eba70bd0deaff1250b187260f7b6d0772bdf111a5
uf50      https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf50-218.tar.gz    a40862e52dfdce78620b037254579a02dbda8182d2879433658a4c15cb00327c
uuf50     https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf50-218.tar.gz   24cc9f492673e0f975fecc56b3a4d8ac21c385cc46205d83b7491a787f43e13d
uf75      https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf75-325.tar.gz    f879d4f619e8cd4b24be6c70b86b1bc1ed851cf0c5cc0ee97cd750e0cadb5ff5
uuf75     https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf75-325.tar.gz   7f8a97aa4d4cbe0d5681746644aac23dc0b5d182065df97e62977716bbccd046
uf100     https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uf100-430.tar.gz   7f691acb8c45790ef8178dd01bb362cf50da608d478be9965599131f0a763e59
uuf100    https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/uuf100-430.tar.gz  736c6f94fecae346a00501b197c482e146b1c6ab05fb6d2e4666e520b8e8508a
aim       https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/AIM/aim.tar.gz      7e4e0076fdd840ed7bcc80c475509ed7726608b010cd3f181d503fe337473c85
dubois    https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/DUBOIS/dubois.tar.gz c0ffe431d4b3fc69226f5f5e0444068d5619642f18f8e4f8c8023c24c9ef263c
pret      https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/PRET/pret.tar.gz    22719743d775f844c73d51b5255c6945ac77c86b6e9205aa718d714ce0006ef2
hole      https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/PHOLE/pigeon-hole.tar.gz 092c4682d1a9d25451e8661af0afa3635943173b07164db495f4f0e11e806ee0
'

# ARCHIVE MEMBER ANSWER: the instances, in the order they are run; the name of an instance is the
# base name of its member, its answer `sat` or `unsat`. Filled below.
INSTANCES=''
for i in 01 02 03 04 05 06 07 08 09 010; do
    INSTANCES+="uf20 uf20-$i.cnf sat"$'\n'
done
for i in 01 02 03 04 05 06 07 08 09 010; do
    INSTANCES+="uf50 uf50-$i.cnf sat"$'\n'
    INSTANCES+="uuf50 UUF50.218.1000/uuf50-$i.cnf unsat"$'\n'
done
for n in 50 100 200; do
    for k in 1_6-yes1-1 1_6-no-1 2_0-yes1-1 2_0-no-1 3_4-yes1-1 6_0-yes1-1; do
        case $k in *-no-*) a=unsat ;; *) a=sat ;; esac
        INSTANCES+="aim aim-$n-$k.cnf $a"$'\n'
    done
done
for i in 01 02 03 04 05 06 07 08 09 010; do
    INSTANCES+="uf75 ai/hoos/Shortcuts/UF75.325.100/uf75-$i.cnf sat"$'\n'
    INSTANCES+="uuf75 UUF75.325.100/uuf75-$i.cnf unsat"$'\n'
done
for i in 01 02 03 04 05 06 07 08 09 010; do
    INSTANCES+="uf100 uf100-$i.cnf sat"$'\n'
    INSTANCES+="uuf100 UUF100.430.1000/uuf100-$i.cnf unsat"$'\n'
done
for i in 20 21 22 25 30 50; do
    INSTANCES+="dubois dubois$i.cnf unsat"$'\n'
done
for i in 60_25 60_75 150_25 150_75; do
    INSTANCES+="pret pret$i.cnf unsat"$'\n'
done
for i in 6 7 8 9; do
    INSTANCES+="hole hole$i.cnf unsat"$'\n'
done
