# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- Solver: naive enumeration of all assignments; returns a satisfying assignment or `Unsat`.
- Verification: `Sat_heap.solver_correct` is proved against `spec/`, with no `sorry`; no input range: every formula of the precondition is answered.
- Framework: the code translates with the AutoCorrode front end without placeholders.
- Benchmarks: none yet; the benchmark measurement is being re-established.
- Tests (auxiliary): `core/tests/`, `tools/fuzz.py` against z3.

## Milestones

- 2026-11-17: verified, top-level theorem `Sat_heap.solver_correct`
- 2026-11-17: the solver returns a satisfying assignment (SAT competition output); specification and proofs updated
