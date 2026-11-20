# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

- **Solver** (`core/src/lib.rs`, 1319 lines): `solver` first runs `cdcl`, an untrusted CDCL
  search, and falls back to the verified DPLL `dpll` (`solve` from the empty assignment, #70) when
  `cdcl` gives up (#45).
  - `cdcl`: iterative trail with decision levels and reasons, first-UIP analysis with backjumping,
    VSIDS-like activities, phase saving, geometric restarts (#45); LBD clause deletion (#51).
  - Data layout: one flat clause arena `arena: Vec<usize>` holding each clause as a header (index,
    end, positions and keys of both watched literals) followed by its literal keys (#71);
    contiguous per-literal watch lists `watches: Vec<Vec<usize>>`, compacted in place during a
    visit, with dead clauses' watch keys set to `NONE` and a `false_lit` array by literal key (#65).
  - Watch visit: a read-only `skip_true` loop passes the run of nodes whose other watched literal is
    true (#81); otherwise `move_watch` scans the clause cyclically from after the later watched
    position (#61, as three plain ranges since #71).
  - Learned clauses: recursive minimisation (MiniSat's `litRedundant` on an explicit stack, new
    theory `Sat_Minimize`, #74); the LBD of a learned clause is lowered when conflict analysis uses
    it (Glucose, #83).
  - Its answers are checked, not its search. `Sat`: `satisfies` checks the model against the
    formula. Learned clauses: `certify` checks before learning that each clause follows from the
    formula and the earlier learned clauses (forced along the trail's reasons). `Unsat`: a certified
    empty clause at level 0. A failed check or exhausted fuel returns `None` → fallback (#45).
  - `solve`: DPLL with unit propagation (cyclic in-place scan) and clause-directed decisions
    (#36, #38, #44).
- **Verification**: `Sat_heap.solver_correct` is proved against `spec/` with no
  `sorry`/`oops`/`quick_and_dirty`; every formula of the precondition is answered. Theories in
  `proof/` (main at b5f85e2, lines): `Sat_Partial` (394, code-independent partial-assignment
  lemmas, #41), `Sat_Proof` (906, DPLL contracts), `Sat_Certify` (609, certificates), `Sat_Search`
  (972, propagation, arena and watch contracts), `Sat_Minimize` (212, minimisation and `analyze`,
  #74), `Sat_CDCL` (168, `cdcl`), `top/Sat_Top` (111, `dpll_spec`, `solver_spec`,
  `solver_correct`). `Sat_CDCL` was split by #54 (review #53). Reviews #63, #68, #76 removed
  unused and wrapper lemmas and merged the bound methods into `search_bound` (#64, #72, #77).
  `isabelle-check` takes 8.5–10 min (progress entries of #65–#83).
- **Framework**: the code translates with the AutoCorrode front end; `urust/PLACEHOLDERS.txt`
  reports 0. The locale `Sat_heap` gained the prism `(64 word) list` for the watch lists (#65, the
  only spec change since #58, by the rule of `CLAUDE.md`). Gaps of `crush_base` found and worked
  around in the code, reported on #34 and #39 (AutoCorrode has issues disabled): two
  cloned-and-updated mutable `Vec<bool>` locals (#34); a lost points-to fact after a call returning
  two `&mut` references, and a field read after such a call; > 4 min on one large loop body (met
  again in #71: slow paths moved into their own functions); `loop` without `break` translating to a
  panic on fuel exhaustion; no split of a `match` on an `Option` result (#39/#45).
- **Benchmark** `Sat-2026-11-18` (the only active suite; 102 SATLIB instances, 20 s / 2 GiB each):
  **102 of 102, 0 wrong; total ≈ 2.3–2.5 s, hole9 ≈ 1.3 s, hole8 ≈ 0.23 s** — the numbers
  reported in PR #83 (min of 3 alternating runs: total 2.32 s, hole9 1.27 s), not from a new run.
  From #51's 4.14 s, the gains were #61 (−11 % total), #65 (−14 %), #71 (−8 %), #74 (−21 %; hole9
  −38 %, but −10 % on permuted copies), #81 (−5.8 % time on hole9 copies,
  same trajectory), #83 (−6 % total; −19 % on 16 fresh hole9 copies). CDCL decides every
  instance itself (#51). Directive #30 compared with z3 on eb3b0a7 (before all of the above): ours
  102 in 4.36 s, z3 102 in 3.86 s; no comparison with z3 has been run since.
- **Tests** (auxiliary): 33 tests — `core/tests/solve.rs` (12, through `solver`),
  `core/tests/dpll.rs` (13: the same cases on `dpll` plus `agrees_with_cdcl` on 200 random 3-CNF
  formulas, #70), `core/tests/cdcl.rs` (8, calling `cdcl` directly and failing on a fallback, #52);
  `tools/fuzz.py` against z3.

## Limitations

- The reference is z3, not Kissat or CaDiCaL: none is installed for the agents (#30).
- The suite is saturated: every instance is decided and hole9 is about half of the total time. Recent
  work measures on permuted copies of hole8/hole9 (variable renaming, polarity, clause and literal
  order), because hole9 itself is luck-prone; those copies are not a benchmark suite under
  `PLAN.md`. Further progress needs a harder suite, which only the owner can add (`PLAN.md`,
  Benchmarks).
- Trusted base (`PLAN.md`): the AutoCorrode translation, the locale `Sat_heap`, and `cli/`.
- The DPLL fallback is never reached on the suite; it is tested directly through `pub fn dpll`
  (#70).
- Dead learned clauses are never freed: `reduce` only sets their watch keys to `NONE`, the arena
  keeps growing (14 MB on hole9, #80). Compacting it was measured in #75 (−2.7 to −3.2 % per
  conflict, below the 5 % aim) and not submitted.
- `proof/Sat_Search.thy` has 972 lines, close to the 1000-line limit; the next contracts of the
  search will need another theory (as `Sat_Minimize` was in #74).
- The Pool Server often answered `server_recovering`/`busy` or failed to open a `dev/` theory
  (sessions of issues #63, #69, #76, #80, #82); several sessions developed with `isabelle-check` alone (~10 min a pass).
- Open PR #86 (issue #85): Glucose dynamic restarts (EMA of LBDs, K = 0.6) instead of the geometric
  schedule; not merged when this summary was written.

### Open leads named by recent sessions

- `certify` costs ≈ 5 % of the time on hole9 (#80): it could check only the reasons conflict
  analysis used (an untrusted hint list), which needs a change of the certification proof.
- One cache miss per watch visit on the clause header that holds the other watched key (77 M of
  143 M D1 misses on hole9, #80). An exact copy of that key in the watch entry cut the misses to
  31 M but gave no time gain (#80); an inline blocker changed the trajectory and was rejected as
  luck (#71, attempt C). The lead left by #75/#78 is fewer words loaded per visit (narrower header
  or arena).
- `pick` is linear in the variables per decision; it is 0.7 % of the instructions on hole9 (#80),
  so it matters only on instances with many more variables.
- Closed without a change: implicit binary watches (#78: binary clauses are 1.2–2.4 % of visits);
  arena compaction (#75, above); a "used" flag sparing clauses from deletion (#82: fewer conflicts
  but +30 % time).

## Milestones

- 2026-11-17: verified, top-level theorem `Sat_heap.solver_correct`
- 2026-11-17: the solver returns a satisfying assignment (SAT competition output); specification and proofs updated
- 2026-11-18: first benchmark suite (#28, renamed `Sat-2026-11-18` by #32); the naive solver solves uf20 only (10 of 102)
- 2026-11-18: backtracking with conflict pruning, 29 of 102 (#36)
- 2026-11-18: unit propagation, 96 of 102 (#38)
- 2026-11-18: in-place propagation with a cyclic scan, 97 of 102 (#44)
- 2026-11-18: CDCL with certified learned clauses, 101 of 102 (#45)
- 2026-11-19: LBD clause deletion and minimisation, 102 of 102 in 4.14 s (#51); directive #30 closed as saturated
- 2026-11-19: cyclic watch scan, contiguous watch lists, flat clause arena (#61, #65, #71); DPLL fallback tested directly (#70)
- 2026-11-19: recursive minimisation and Glucose LBD update (#74, #83); 102 of 102 in ≈ 2.3–2.5 s, hole9 ≈ 1.3 s (#83)
