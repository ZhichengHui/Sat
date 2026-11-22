# Progress

The state and milestones of this repository, kept up to date by summarize sessions (see `PLAN.md`).
Per-session details are in `progress/`.

## Current state

Main at 797a705 (#123). Line counts and the benchmark line were measured this session; everything
else comes from the PR or progress entry named.

- **Solver** (`core/src/lib.rs`, 1533 lines): `solver` first runs `cdcl`, an untrusted CDCL
  search. If `cdcl` gives up, `solver` falls back to the verified DPLL `dpll` (#45, #70).
  - `cdcl`: iterative trail with decision levels and reasons, first-UIP analysis with backjumping,
    and phase saving (#45).
    - VSIDS-like activities with a slow decay: the increment grows by `inc / 512 + 1`, decay
      ≈ 0.998 (#95). MiniSat's 0.95 and every faster decay were worse on hole8/hole9.
    - Glucose dynamic restarts (#86): fast EMA of LBDs against the overall average, at least
      50 conflicts apart. The constant K is 0.7 since #114; #86 used 0.6.
    - LBD clause deletion (#51): first reduction after 1000 conflicts, each interval 500 longer
      than the last; about half of the live learned clauses deleted by an LBD cut-off that never
      goes below 4.
  - Data layout:
    - One flat clause arena `arena: Vec<usize>` (#71).
    - Contiguous per-literal watch lists (#65). Since #105 a watch node is the arena position of
      the other watched key, which is read without loading the clause header.
    - Every vector grows only while it is shorter than `BIG` = 2^56, and the search gives up if
      a vector reaches that bound (#105). Activities use a separate bound `ACT` = 2^62.
    - Each guard has a doc comment naming its proof obligation (#115).
  - Learned clauses:
    - Recursive minimisation (#74). LBD updated when analysis uses a clause (Glucose, #83).
    - `copy_learnt` allocates each clause at once (`Vec::with_capacity`, guarded by `BIG`, #120).
  - Its answers are checked, not its search:
    - `Sat`: `satisfies` checks the model.
    - Learned clauses: `certify` checks each clause before it is learned (#45).
      - Since #116, `certify` re-checks only the reasons that conflict analysis used. Analysis
        passes it an untrusted hint list: the resolved variables and the variables minimisation
        removed. The mark buffer is kept in `Search` between calls.
      - A wrong hint can only make the check fail (#123 documents why).
    - `Unsat`: a certified empty clause at level 0.
    - A failed check or exhausted fuel returns `None`, and `solver` falls back to DPLL.
  - `dpll`/`solve`: DPLL with unit propagation and clause-directed decisions (#36, #38, #44).
  - `cli/` ignores an empty clause read after the header's clause count, with a warning (#111).
    SATLIB's pret files end with a lone `0`, so until #111 pret was decided "unsat" without any
    search. On pret150_25 with one clause removed (satisfiable), main gave a **wrong UNSAT**
    before #111.
- **Verification**: `Sat_heap.solver_correct` is proved against `spec/` with no
  `sorry`/`oops`/`quick_and_dirty` (grep on main this session).
  - Since #105 the precondition also requires `sat_sizes_ok` (number of variables < 2^63),
    besides `sat_repr_ok` and `formula_invariant`.
  - Theories in `proof/` (lines, `wc -l` this session):
    - `Sat_Partial` 451, `Sat_Proof` 909 (DPLL contracts).
    - `Sat_Certify` 742 (certificates, incl. the hint passes of #116).
    - `Sat_Vectors` 379 (new in #105: `rvec` lemmas, the search invariant `sok`/`vok`, the
      method `sok_asm`).
    - `Sat_Search` 810 (propagation, arena and watch contracts; 972 before #93/#105).
    - `Sat_Minimize` 254, `Sat_Reduce` 185 (deletion and restarts, split off by #93).
    - `Sat_CDCL` 250, `top/Sat_Top` 123.
  - `spec/`: `Formula_Types` 53, `Sat_Spec` 174.
  - Proof time:
    - The session `Sat_Proof` runs with `parallel_proofs = 0` since the repair of PR #92. Forked
      proofs in `Sat_Search` failed on CI runners with "Cannot transfer: not a super theory".
    - `isabelle-check` took 4:29 in #95, about 9 min in #115, and 17 min under heavy load in #123
      (progress entries).
- **Framework and spec changes**:
  - #105 (owner-approved on #98, option (a)): migration to front end 236538c, which models
    `Vec<T>` as `T rvec`.
    - `spec/`: the shape lemmas and `clause_sat`/`formula_sat`/`formula_invariant` read
      `rvec_elems`, and `sat_repr_ok` uses `rvec_length`.
    - New precondition `sat_sizes_ok`.
    - The locale `Sat_heap` takes the prisms `bool rvec`, `(64 word) rvec`, `64 word`, `Search`,
      `Clause rvec`, `Lit rvec`.
    - `tools/spec.sha256` updated in that PR.
    - Preparation: report #102, trial on #98 (session 67db04ed).
  - `urust/PLACEHOLDERS.txt` reports 0.
  - Gaps of `crush_base`:
    - The gaps reported on #34 and #39 still stand. AutoCorrode has issues disabled, so the
      reports are on those issues.
    - Found by #105:
      - There is no modify rule for `rvec_elems_focus`, so the proofs define their own.
      - A premise `sok s` can instantiate the postcondition's `sok ?s'` before the points-to
        fact is matched. Workaround: the alias `sok_in`.
- **Benchmark** `Sat-2026-11-18` (the only active suite; 102 SATLIB instances, 20 s / 2 GiB each):
  - **102 of 102, 0 wrong; total 1.34 s, hole9 0.44 s, hole8 0.08 s.** One run of
    `bench/run.sh` on a release build of main 797a705 this session, at load ≈ 19–21.
  - Changes reported by the PRs since #83, all measured as the minimum of 3 alternating runs:

    | PR | change | suite total | hole9 | measured on |
    |---|---|---|---|---|
    | #83 | — | 2.32 s | 1.27 s | the suite |
    | #86 | restarts | — | −11 % | the suite |
    | #95 | VSIDS decay | 2.11 → 1.75 s | 0.99 → 0.64 s | the suite |
    | #105 | rvec, watch node | 1.70 → 1.65 s | — | the suite |
    | #105 | rvec, watch node | — | −5.6 to −5.8 % | fresh hole9 copies |
    | #114 | K = 0.7 | 1.61 → 1.41 s | 0.61 → 0.45 s | the suite |
    | #116 | `certify` hint | 1.38 → 1.33 s | — | the suite |
    | #116 | `certify` hint | — | −4.1 % | permuted hole8/hole9 copies |
    | #120 | `with_capacity` | 1.47 → 1.45 s | — | the suite |
    | #120 | `with_capacity` | — | — | fresh uuf100 + hole7 copies: −3.0 % |

  - Most of the time on the 100 small instances is the harness (#100): about 7.7 ms per
    instance in `bench/run.sh`, against about 1.7 ms of solver work.
  - Directive #30 compared with z3 on eb3b0a7 (ours 4.36 s, z3 3.86 s). No comparison has been
    run since.
- **Tests** (auxiliary): 36 tests, all passing (`cargo test --release` this session).
  - `core/tests/solve.rs`: 12 tests.
  - `core/tests/dpll.rs`: 13 tests, incl. `agrees_with_cdcl`.
  - `core/tests/cdcl.rs`: 8 tests.
  - `cli/` unit tests: 3, for the trailing empty clause of #111.
  - `tools/fuzz.py` tests the solver against z3.
- **Lessons**: `LESSONS.md` (#92) collects the lessons of #61–#86.

## Limitations

- The reference is z3, not Kissat or CaDiCaL: none is installed for the agents (#30).
- The suite is saturated.
  - Every instance is decided; hole9 is a third of the total, and the harness is most of the rest
    (#100).
  - Tuning work measures on permuted copies of hole7/hole8/hole9 and uuf100 (variable renaming,
    polarity, clause and literal order). These copies are not a benchmark suite under `PLAN.md`.
  - The constants chosen on them (decay 0.998, K = 0.7) are tuned to pigeon-hole instances. On
    random 3-SAT, uuf100 never restarts with K = 0.7 and rarely reaches the first `reduce` (#106).
  - Further progress needs a harder suite, which only the owner can add (`PLAN.md`, Benchmarks).
- Trusted base (`PLAN.md`): the AutoCorrode translation, the locale `Sat_heap`, and `cli/`.
  - `cli/` produced a wrong answer on a modified pret file until #111 (see above).
  - z3 `-dimacs` and `bench/check-model.py` still read a trailing lone `0` as an empty clause
    (#111). Changing `bench/` needs the owner.
- `solver_correct` covers only formulas with fewer than 2^63 variables (`sat_sizes_ok`, #105).
- The DPLL fallback is never reached on the suite. It is tested directly through `pub fn dpll`
  (#70).
- Dead learned clauses are never freed, and the arena keeps growing (14 MB on hole9, #80).
  Compaction measured −2.7 to −3.2 % per conflict (#75), below the 5 % aim, and was not
  submitted.
- The Pool Server was unreliable under load: `server_recovering`, http 500 and "scratch pool
  exhausted" in #114, #115, #116, #123.
  - Most sessions checked with `isabelle-check` alone, 9–17 min a pass.
  - Heap builds are refused because `Sat_Partial` has an `ML` command (#116).
- During #98 (session 67db04ed), a faulty kill script sent SIGTERM to about 390 of the user's
  processes, including warm Pool Server sessions. The lesson is recorded in that progress entry.

### Negative results since #88 (closed without a PR)

- #96, deletion schedule: no variant met the gate.
  - The best fresh hole9 result was −8.7 %, but it was +5 % on hole8 and did not reproduce on the
    first set.
  - The LBD protection bound changes nothing on the hole instances.
  - The schedule of #51 stays.
- #97, partial restarts (trail reuse): −1.9 % on fresh hole9 against a 5 % gate.
  - Restarts undo ≤ 0.22 % of the assignments on hole8/hole9, so the ceiling is tiny.
  - The paper's "keep the level" variant was +11 %.
- #100, profile of the 100 small instances:
  - Read, parse and output in `cli/` are ≈ 1.3 % of their time.
  - About 74 % is the `bench/run.sh` harness and about 10 % process creation.
  - Also found: the pret files end in a lone `0` (fixed by #111).
- #102: report for the owner on what the rvec front end breaks, with a trial port. It fed the
  decision on #98 and #105. No PR by design.
- #106, profile of uuf100/hole7:
  - `propagate` 56–62 % of the instructions, `analyze` 17–22 %, `certify` 9–10 %, `pick`
    1.5–4.7 %.
  - Its PR #117 was closed as superseded by #116.
  - Its `with_capacity` commit landed as #120.

### Open leads

- Propagation is 56–62 % of the instructions (#106). One cache miss per visit on the clause
  header was the lead of #80. #105 removed the header read for the other watched key; fewer words
  per visit remain a lead.
- `pick` is linear in the variables: 4.7 % of the instructions on uuf100 (#106). A heap matters
  only on instances with many more variables.
- Closed without a change earlier: implicit binary watches (#78), arena compaction (#75), a
  "used" flag on learned clauses (#82), a faster VSIDS decay (#95's measurement), the deletion
  schedule (#96), trail reuse (#97).

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
