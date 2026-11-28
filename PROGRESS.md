# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

Main at 0b2feb1 (#151). Line counts, the test count, the `sorry` grep and the benchmark line were
measured this session; everything else comes from the PR, issue comment or progress entry named.
#154 (review of #149) was still open when this was written.

- **Solver** (`core/src/lib.rs`, 1891 lines; 1533 at #123): `solver` first runs `cdcl`, an
  untrusted CDCL search. If `cdcl` gives up, `solver` falls back to the verified DPLL `dpll`
  (#45, #70).
  - `cdcl`: iterative trail with decision levels and reasons, first-UIP analysis with backjumping,
    and phase saving (#45).
    - VSIDS-like activities with a slow decay: the increment grows by `inc / 512 + 1`, decay
      ≈ 0.998 (#95).
    - **Reason-side bumping** (#132, gate changed by #138): `analyze` also bumps the variables of
      the reasons of the learned clause's literals (`bump_reasons`), but only while the fast
      moving average of LBDs of the restarts (`fast`, weight 1/32) is at least 6.5. Pigeon-hole
      instances learn LBD 7–15 and need about 40 % fewer conflicts with it; uuf100 learns LBD
      4.3–5.2 and needs more (#133's entry). #132 gated on the cumulative average `lbd_sum / nconf`,
      which bumped during the first conflicts of uuf100 (+5–6 % there); #138's gate on `fast`
      brought uuf100 back to its pre-#132 time.
    - **Variable heap** (#144, tidied by #151): with at least `HEAP_MIN` = 512 variables, `pick`
      pops a binary max-heap keyed on (activity desc, index asc), the exact order of the old scan,
      so every decision is the same as before. Below 512 variables `pick` keeps the linear scan
      (an always-on heap was 3–5 % slower on uuf100/hole copies). The heap code is
      `#[inline(never)]`: inlined, it cost +1.4 % instructions in `cdcl` on hole9 even when off.
    - Glucose dynamic restarts (#86), K = 0.7 (#114).
    - LBD clause deletion (#51): first reduction after 1000 conflicts, each interval 500 longer
      than the last; about half of the live learned clauses deleted by an LBD cut-off that never
      goes below 4.
  - Data layout:
    - One flat clause arena `arena: Vec<usize>` (#71); contiguous per-literal watch lists (#65);
      a watch node is the arena position of the other watched key (#105).
    - Every vector grows only while it is shorter than `BIG` = 2^56, and the search gives up if
      a vector reaches that bound (#105). Activities use a separate bound `ACT` = 2^62. Each guard
      has a doc comment naming its proof obligation (#115).
    - The heap vectors `heap`/`hpos` have fixed length `n`, so `sok` says nothing about the heap.
  - Learned clauses: recursive minimisation (#74), Glucose LBD update (#83), `copy_learnt` with
    `Vec::with_capacity` (#120).
  - Its answers are checked, not its search:
    - `Sat`: `satisfies` checks the model.
    - Learned clauses: `certify` checks each clause before it is learned (#45).
      - Since #116, `certify` re-checks only the reasons that conflict analysis used, from an
        untrusted hint list.
      - Since #149, also only the **level-0 reasons the conflict needs**: `level0_hint` builds the
        untrusted list `hint0` by a post-order DFS over the level-0 reasons of the conflict clause
        and of the hinted reasons. It does so only if the level-0 prefix is longer than `hint`
        (`lim[0] > hint.len()`); otherwise `certify` re-forces the whole prefix as before. On bmc
        the prefix is 3k–27k variables, of which 80–248 are needed; on uuf100/hole it is about
        one variable, where the always-on DFS cost about 3 % (#148's entry).
      - A wrong hint can only make the check fail (#123, #149).
    - `Unsat`: a certified empty clause at level 0.
    - A failed check or exhausted fuel returns `None`, and `solver` falls back to DPLL.
  - `dpll`/`solve`: DPLL with unit propagation and clause-directed decisions (#36, #38, #44).
  - `cli/` ignores an empty clause read after the header's clause count, with a warning (#111).
- **Verification**: `Sat_heap.solver_correct` is proved against `spec/` with no
  `sorry`/`oops`/`quick_and_dirty` (grep on main this session; `tools/check-spec.sh` passes).
  - The precondition is `sat_repr_ok`, `formula_invariant` and `sat_sizes_ok` (number of
    variables < 2^63, #105). The locale `Sat_heap` and `spec/` did not change since #105: #132,
    #144 and #149 added `Search` fields (`heap`, `hpos`, `hlen`, `use_heap`, `hint0`) but no prism.
  - Theories in `proof/`, in session order (lines, `wc -l` this session; at #123 in brackets):
    - `Sat_Partial` 451 (451), `Sat_Proof` 909 (909): DPLL contracts.
    - `Sat_Certify` 750 (742): certificates and the hint passes.
    - `Sat_Vectors` 379 (379): `rvec` lemmas, the invariant `sok`/`vok`, the method `sok_asm`.
    - `Sat_Heap` 239 (new in #144; 281 before #151's `heap_crush`): the heap contracts and `pick`.
    - `Sat_Search` 785 (810): propagation, arena, watch, `bump`/`rescale`/`backtrack` contracts.
    - `Sat_Minimize` 387 (254): analysis, minimisation, reason bumping (#132), and the rules and
      method `sok_fast` of #146.
    - `Sat_Reduce` 186 (185): deletion and restarts.
    - `Sat_Level0` 171 (new in #149): the `hint0` DFS; its method `sok0` is `sok_fast` with a
      `sok_hint0` rule. #154 (open) brings it to 140.
    - `Sat_CDCL` 259 (250), `top/Sat_Top` 123 (123).
  - `spec/`: `Formula_Types` 53, `Sat_Spec` 174 (unchanged).
  - Proof time:
    - `Sat_Proof` forks proofs again since #136 (`parallel_proofs = 0` dropped; three CI runs
      without "Cannot transfer"; `Sat_Proof` 42–55 % faster on CI, normalised by AutoCorrode).
    - #140 reordered proof steps (cheap, specific rules such as `sok_asm` before the `auto`-based
      `sok_tac`/`cdcl_bound`): batch `Sat_Proof` 931 s → 350 s elapsed, 2111 s → 1177 s CPU;
      `Sat_CDCL` 868 s → 235 s, `Sat_Certify` 270 s → 100 s cumulated.
    - #146 did the same for `Sat_Minimize` with `sok_fast`: 211.6 s → 126.3 s cumulated. The
      session time did not move: the critical path is `Sat_Search` → `Sat_CDCL`.
    - What is left of the slowest steps is `crush_base` itself (≈ 110 s in `cdcl_spec`, 85 s in
      `Search_propagate_lit_spec`), which cannot be reduced without changing AutoCorrode.
    - `isabelle-check`: 16 min in #133/#134 (before #140), 7:04–7:31 in #144, #146, #149 and #151.
- **Framework and spec changes**: none since #105 (owner-approved on #98, migration to front end
  236538c, `Vec<T>` as `T rvec`). `urust/PLACEHOLDERS.txt` reports 0 (this session).
  - Gaps of `crush_base`: those reported on #34 and #39 still stand (AutoCorrode has issues
    disabled). #105 found that there is no modify rule for `rvec_elems_focus` and that a premise
    `sok s` can instantiate the postcondition's `sok ?s'` too early (workaround `sok_in`).
  - The front end ignores `#[inline(never)]` and doc comments, so they do not change `urust/`.
- **Benchmark** `Sat-2026-11-18` (the only active suite; 102 SATLIB instances, 20 s / 2 GiB each):
  - **102 of 102, 0 wrong; total 1.34 s, hole9 0.29 s, hole8 0.06 s, hole7 0.03 s.** One run of
    `bench/run.sh` on a release build of main 0b2feb1 this session, at load ≈ 2.5.
  - Changes reported by the PRs since #123, all as the minimum of 3 alternating runs:

    | PR | change | suite total | hole9 | other measurement |
    |---|---|---|---|---|
    | #132 | reason bumping | 1.27 → 0.90 s | 0.44 → 0.13 s | fresh hole9 copies −43 % / −60 % |
    | #138 | gate on `fast` | 1.13–1.17 → 1.31–1.32 s | 0.13 → 0.28 s | uuf100 ×10 + hole7 copies −3.9 to −5.2 %; uuf100 alone back to pre-#132 |
    | #144 | variable heap | 1.27 → 1.27 s | 0.28 → 0.28 s | bmc 34.68 → 23.37 s (−32.6 %) |
    | #149 | `hint0` | 1.29 → 1.29 s | — | bmc 23.63 → 12.15 s (−48.6 %) |

    #138 made the original hole9 slower on the suite (one trajectory: #132's gain there was
    luck), but faster on 64 fresh copies (−7.2 %). The suite total is again about the 1.34 s of
    #123; the gains of #132–#149 are on the copies and on bmc, not on the suite.
  - Most of the time on the 100 small instances is the harness (#100): about 7.7 ms per
    instance in `bench/run.sh`, against about 1.7 ms of solver work.
- **Against z3** (#141, on main 187a7b1, before #138/#144/#149; z3 5.4.1, 60 s / 2 GiB, solver
  time only, full tables on #141):
  - No wrong answer, crash or disagreement on 2219 instances in 32 SATLIB families plus the suite.
  - Suite: ours 0.83 s, z3 3.18 s (hole9 0.14 s vs 1.93 s). hole10: 0.76 s vs 5.8 s.
    uuf250: 460 s vs 746 s.
  - We lose on bmc (58.8 s vs 6.1 s), hanoi5 (25.3 s vs 7.6 s), sub-second ais, bw_large.d,
    par16, flat175/200 (2–10×), and uf/uuf150–200 (1.2–1.5×).
  - Since then, bmc on our side: 34.7 s after #138 (#143's baseline), 23.4 s after #144,
    12.2 s after #149 (#148's entry). These are separate measurements on our side only; no
    z3 run has been repeated, so the bmc gap is now roughly 2× by these numbers, not measured.
  - par32 (10/10) times out for both solvers at 60 s.
- **Tests** (auxiliary): 36 tests, all passing (`cargo test --release` this session):
  `core/tests/` (solve, dpll incl. `agrees_with_cdcl`, cdcl) and 3 `cli/` unit tests. `tools/fuzz.py`
  tests the solver against z3; #144 also fuzzed with the heap forced on (`HEAP_MIN = 0`).
- **Lessons**: `LESSONS.md` (218 lines; #92, extended by #127 with #93–#125).

## Limitations

- The reference is z3, not Kissat or CaDiCaL: none is installed for the agents (#30).
- The suite is saturated and no longer measures the work being done.
  - Every instance is decided in about 1.3 s, most of it harness (#100). #144 and #149 left the
    suite total unchanged and were judged on bmc instances outside it, with the suite and
    permuted hole/uuf100 copies as guards.
  - The permuted copies and the bmc/hanoi instances are not benchmark suites under `PLAN.md`.
    #141 lists material for a graded harder suite (bmc, hanoi4/5, uf/uuf250 samples, flat200,
    bw_large.c/d, hole10, par32); adding it is the owner's decision (`PLAN.md`, Benchmarks).
  - Constants were tuned on pigeon-hole and uuf100 (decay 0.998, K = 0.7, LBD 6.5). #141 found
    that the structured families (bmc, hanoi) are where we fall behind.
- Trusted base (`PLAN.md`): the AutoCorrode translation, the locale `Sat_heap`, and `cli/`.
  - z3 `-dimacs` and `bench/check-model.py` still read a trailing lone `0` as an empty clause
    (#111). z3 also omits don't-care variables from its models, which `check-model.py` rejects
    (#141). Changing `bench/` needs the owner.
- `solver_correct` covers only formulas with fewer than 2^63 variables (`sat_sizes_ok`, #105).
- `solver_correct` says nothing about speed or about the heap or hints being right: they are
  untrusted, and a wrong one only makes a check fail and the solver fall back to DPLL.
- The DPLL fallback is never reached on the suite. It is tested directly through `pub fn dpll`
  (#70).
- Dead learned clauses are never freed, and the arena keeps growing (14 MB on hole9, #80).
- The Pool Server was unreliable under load (`server_recovering` for a whole session in #133);
  most sessions check with `isabelle-check` or batch builds on task heaps (#139, #145).

### Negative results since #123 (closed without a PR or not merged)

- #129, reason-side bumping always on: uuf100 +32 % / +36 % time; led to the gated #132.
- #134 (in #138's entry): bumping each reason variable at most once per conflict doubled hole9's
  conflicts; no early-LBD signal separates hole7 from uuf100.
- #148 option (b), resetting only the touched marks of `cleared`: needs an invariant on the marks
  across calls in `sok`; not done.
- #150: removing the redundant `self.use_heap &&` in `insert` would change the code of an
  `#[inline(never)]` function; left for a measured change.

### Open leads

- bmc after #149 (#148's entry, galileo-9): `cdcl`'s propagation 71 % of the instructions,
  `backtrack` 6 %, the memset of `cleared` 5.3 %, `close0` 4.3 %.
- hanoi5: 25.3 s vs z3 7.6 s in #141. #143 and #148 measured main at about 48–50 s on hanoi5 under
  their own harness (after #138); neither the heap (−2.2 %) nor `hint0` (−1.9 %) helped. The gap
  between 25 s and 50 s was not explained by those entries.
- par32 is unsolved by both solvers at 60 s (#141).
- uf/uuf150–200 are 1.2–1.5× slower than z3 (#141).
- Closed without a change earlier: implicit binary watches (#78), arena compaction (#75), a
  "used" flag on learned clauses (#82), a faster VSIDS decay (#95), the deletion schedule (#96),
  trail reuse (#97).

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
- 2026-11-19: Glucose dynamic restarts (#86); `LESSONS.md` (#92); `Sat_Search` split, new theory `Sat_Reduce` (#93)
- 2026-11-20: slower VSIDS decay, suite 2.11 → 1.75 s, hole9 0.99 → 0.64 s (#95); CI proofs sequential inside `Sat_Proof` (`parallel_proofs = 0`, repair of #92)
- 2026-11-21: rvec migration of `spec/` and `proof/` (owner-approved #98), `BIG` = 2^56 guards, watch node = arena position of the other watched key, new theory `Sat_Vectors` (#105, tidied by #115)
- 2026-11-21: `cli/` ignores a trailing empty clause after the header's count; fixes a wrong UNSAT on modified pret files (#111)
- 2026-11-21: Glucose restart K = 0.7, suite 1.61 → 1.41 s, hole9 0.45 s (#114)
- 2026-11-22: `certify` checks only the reasons analysis used (untrusted hint, #116, tidied by #123); `copy_learnt` with `Vec::with_capacity` (#120); 102 of 102 in 1.34 s, hole9 0.44 s (this summary's run)
- 2026-11-22: `LESSONS.md` extended with #93–#125 (#127); adaptive reason-side bumping, suite 1.27 → 0.90 s, fresh hole9 copies −43 % / −60 % (#132, tidied by #137)
- 2026-11-23: `Sat_Proof` forks proofs again (#136); targeted proof steps, batch `Sat_Proof` 931 s → 350 s (#140); reason bumping gated on the fast LBD average, uuf100 back to pre-#132 (#138)
- 2026-11-23: main vs z3 on the suite and 2219 SATLIB instances: no disagreement; we win on the suite, hole10, uuf250 and lose on bmc and hanoi5 (#141, entry #142)
- 2026-11-27: variable heap for `pick` on ≥ 512 variables, bmc −32.6 %, new theory `Sat_Heap` (#144, tidied by #151); `sok_fast` in `Sat_Minimize`, 211.6 s → 126.3 s (#146)
- 2026-11-28: `certify` checks only the level-0 reasons the conflict needs (untrusted `hint0`), bmc −48.6 %, new theory `Sat_Level0` (#149); 102 of 102 in 1.34 s, hole9 0.29 s (this summary's run)
