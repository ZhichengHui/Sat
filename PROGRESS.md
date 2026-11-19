# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- **Solver** (`core/src/lib.rs`, 1036 lines): `solver` first runs `cdcl`, an untrusted CDCL
  search, and falls back to the verified DPLL `solve` when `cdcl` gives up (#45).
  - `cdcl`: iterative trail with decision levels and reasons, two watched literals, first-UIP
    analysis with backjumping, VSIDS-like activities, phase saving, geometric restarts (#45); LBD
    clause deletion, cached watch keys, local learned-clause minimisation (#51).
  - Its answers are checked, not its search. `Sat`: `satisfies` checks the model against the
    formula. Learned clauses: `certify` checks before learning that each clause follows from the
    formula and the earlier learned clauses (forced along the trail's reasons). `Unsat`: a certified
    empty clause at level 0. A failed check or exhausted fuel returns `None` → fallback (#45).
  - `solve`: DPLL with unit propagation (cyclic in-place scan) and clause-directed decisions
    (#36, #38, #44).
- **Verification**: `Sat_heap.solver_correct` is proved against `spec/` with no
  `sorry`/`oops`/`quick_and_dirty`; every formula of the precondition is answered. Theories in
  `proof/` (main at eb3b0a7): `Sat_Partial` (code-independent partial-assignment lemmas, #41),
  `Sat_Proof` (DPLL contracts), `Sat_CDCL` (1735 lines: certificates and all CDCL contracts),
  `top/Sat_Top` (`solver_spec`, `solver_correct`). Open PR #54 (review #53) splits `Sat_CDCL` into
  `Sat_Certify`, `Sat_Search`, `Sat_CDCL`.
- **Framework**: the code translates with the AutoCorrode front end; `urust/PLACEHOLDERS.txt`
  reports 0. Gaps of `crush_base` found and worked around in the code, reported on #34 and #39
  (AutoCorrode has issues disabled): two cloned-and-updated mutable `Vec<bool>` locals (#34); a
  lost points-to fact after a call returning two `&mut` references, and a field read after such a
  call; > 4 min on one large loop body; `loop` without `break` translating to a panic on fuel
  exhaustion; no split of a `match` on an `Option` result (#39/#45).
- **Benchmark** `Sat-2026-11-18` (the only active suite; 102 SATLIB instances, 20 s / 2 GiB each):
  **102 of 102 in 4.14 s, 0 wrong** (#51); hole9 3.06 s, hole8 0.30 s. A build whose fallback
  panics also solves 102/102, so CDCL decides every instance itself (#51). Directive #30 compared
  it with z3 on main eb3b0a7: ours 102 in 4.36 s, z3 102 in 3.86 s; the gap is hole7–9 (about
  1.6× on hole9).
- **Tests** (auxiliary): `core/tests/solve.rs` (12 tests, through `solver`), `core/tests/cdcl.rs`
  (8 tests calling `cdcl` directly and failing on a fallback, #52); `tools/fuzz.py` against z3.

## Limitations

- The reference is z3, not Kissat or CaDiCaL: none is installed for the agents (#30).
- The suite is saturated: every instance is decided and the times are close to z3's. Further
  progress needs a harder suite, which only the owner can add (`PLAN.md`, Benchmarks).
- Trusted base (`PLAN.md`): the AutoCorrode translation, the locale `Sat_heap`, and `cli/`.
- The DPLL fallback is never reached on the suite; it is tested directly through `pub fn dpll` (#69).
- Known costs not addressed: `pick` is linear in the variables per decision; `certify` scans every
  trail reason; dead learned clauses are never freed (#51, review #48). The module comment of
  `core/src/lib.rs` still describes only the DPLL solver.
- `proof/Sat_CDCL.thy` exceeds the 1000-line limit (being split in PR #54).

## Milestones

- 2026-11-17: verified, top-level theorem `Sat_heap.solver_correct`
- 2026-11-17: the solver returns a satisfying assignment (SAT competition output); specification and proofs updated
- 2026-11-18: first benchmark suite (#28, renamed `Sat-2026-11-18` by #32); the naive solver solves uf20 only (10 of 102)
- 2026-11-18: backtracking with conflict pruning, 29 of 102 (#36)
- 2026-11-18: unit propagation, 96 of 102 (#38)
- 2026-11-18: in-place propagation with a cyclic scan, 97 of 102 (#44)
- 2026-11-18: CDCL with certified learned clauses, 101 of 102 (#45)
- 2026-11-19: LBD clause deletion and minimisation, 102 of 102 in 4.14 s (#51); directive #30 closed as saturated
