# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed. Progress entries are cited by session prefix (`progress/*_<prefix>.md`).

## Tooling: Pool Server and batch checks

- **The Pool Server is often unusable, worst under load.** `isabelle_open` answers `busy`, HTTP 500
  or `server_recovering`, sometimes for a whole session (c465b40d, b64c1dfb, 7f86250c, f381ca7f,
  2f71a521; http 500 on files importing `Sat_Reduce` at load 30–50: d4428027, 1ff7d271). Retry once
  with a fresh `task_group` (the issue number); that worked in c3e0f79e, adea3d20, 8468478b. If it
  fails again, do not spend the session on it: fall back to batch checks (below). Since #105 most
  sessions verified with `isabelle-check` alone (2f71a521, fe122830, d4428027, 20c72b96).
- **`isabelle-check` is a workable loop** (4.5–17 min a pass, depending on load: 3a4b8b22,
  fe122830, 1ff7d271). Batch several fixes per pass.
- **Faster batch passes**: a task heap of the unchanged theories built with `isabelle build` and a
  ROOT entry (up to `Sat_Search`: 11 min), and a second session holding only the changed theories,
  ≈ 12 min a pass (81673216; earlier 3b9d4646, adea3d20). Two sessions cannot share a directory in
  one ROOT: give the second its own. `isabelle_build_heap` cannot build these heaps ("Cannot load
  theory Micro_Rust_Std_Lib"; refused since `Sat_Partial` has an `ML` command: d4428027). Delete the
  heap afterwards. `isabelle-check` ignores the options of `proof/ROOT` (it builds one task session).
- **Batch-only recipe.** End an unfinished step with `done` (not `sorry`): "Failed to finish proof"
  prints the remaining goals. `isabelle build_log -H Error <session>` shows every error with its
  full goal; `check.log` truncates them (b64c1dfb, adea3d20). Watch the log for "running for"
  > 180 s (81673216).
- **Stale state in the Pool Server.** It keeps the imported theories it loaded at `isabelle_open`:
  after regenerating `urust/` and `isabelle-devcopy`, close and reopen the file (1da7f95e). Editing
  a file while it is being checked, or a line above a finished `crush_base`, gives spurious "Cannot
  join unrelated theory certificates": wait, or `isabelle_close` with `destroy` and reopen
  (adea3d20, 9f3404cc, b0b18b19).
- **`isabelle_multi_attempt` rarely gets a scratch session** ("scratch pool exhausted": c3e0f79e,
  adea3d20, fe122830). Try steps by editing the file and re-checking in place.
- **One hanging `metis`/`blast`/`auto` stalls a whole batch build** for its time limit; plain `auto`
  hangs on goals with large record-update premises, `sok_tac` (`auto`) ran > 5 min on `cdcl`'s main
  loop. Prefer `rule`/`simp` steps and targeted lemmas (`sok_lim_push`, `sok_lbd_dead`)
  (b64c1dfb, adea3d20, 81673216).
- **A proof that fails only in CI with "Cannot transfer: not a super theory"** was a timing race
  between forked proofs on the slower runners, not a wrong proof; `proof/ROOT` now sets
  `parallel_proofs = 0` for `Sat_Proof` (53f8b137 / #92). Keep it; check locally before rewriting.
- **Killing processes**: a script that computed a kill list (awk over `ps`) sent SIGTERM to ~390
  processes of the user, among them Pool Server sessions and other agents' work (67db04ed / #98).
  List the children with `ps --ppid` and kill named PIDs only.
- `coordination create-pr --help` is not help: it tries to create a PR (b64c1dfb).

## Writing code that `crush_base` can verify

AutoCorrode has issues disabled: report gaps on the project issue (as on #39, #34), and change the
code to avoid them. Known gaps and the workarounds that held:

- **Two mutable references from one call**: after a call whose contract returns two `&mut` results
  (or with two mutable `Vec<bool>` locals updated in turn), a points-to fact is lost. Give no
  function two `&mut` arguments; keep extra data as a field of the state record (b64c1dfb,
  adea3d20). To lend a field to a helper, make the helper a method that takes the field with
  `mem::replace` and stores it back (#113).
- **After a `&mut self` call the caller knows only what its contract says** (`∃ s'`): do the other
  writes first and the call last (41040648), and re-check a bound the code needs after the call
  when the callee's contract does not keep it (c2676fcb / #82).
- **Large loop bodies are slow**: `crush_base` took > 4 min on the CDCL loop body (adea3d20, 9f3404cc).
  One loop per function; move slow paths into their own functions. Inside a big body write offsets
  as `if side == 0 { o + 5 } else { o + 4 }`; arithmetic like `o + 5 - side` is fine in a small
  function with a lemma; in Rust an `if side` select can become a branch (+15 %: f381ca7f / #80).
- **Sequential `if`s multiply `crush_base`'s paths**: seven guarded updates in a row ran > 3 min;
  one block under a combined guard took ~1 min (b0b18b19).
- **`loop` without `break`** translates to `panic!("unreachable …")` when fuel runs out; use
  `while cond` (adea3d20). **Avoid `continue`**; write an if/else chain (41040648). **`match` on an
  `Option` result is not split**: `cases x` and `simp only: option.case` first (adea3d20).
- **Guards instead of relational invariants**: check `i < len` before `i += 1`, `v < x.len()` before
  an index, so no invariant relating lengths is needed (41040648, adea3d20, 9f3404cc).
- **Under the rvec model every growing vector needs a length guard.** `Vec<T>` is `T rvec` since
  front end 236538c (#98/#105). A push is proved not to overflow only under `rvec_wf` and a bound:
  `BIG = 2^56`, a `len() < BIG` guard before every push (a push of ≤ 8 elements then fits:
  `vok_append`), give-up guards for counters, guarded `vec![x; n]`. Keep a constant that steers the
  search (activities: `ACT = 2^62`) separate from `BIG`, so the trajectory does not change
  (67db04ed, 81673216). No guard is implied by another (fe122830 / #108); do not remove one without a
  proof that still goes through.
- **Constants of `lib.rs` appear in word lemmas.** Changing `inc / 32` to `inc / 512` broke
  `inc_div` (it names `0x20`); `restart_due`'s `3`/`5` → `7`/`10` broke `restart_avg`. Before the
  first check, grep `proof/` for the old constant (3a4b8b22, 2f71a521).
- **A new mutable local of a new type adds a prism** to the locale `Sat_heap` in `spec/`: then
  update the locale, the prism list of `solver`, and `Sat_ctxI` in `proof/top/Sat_Top.thy`
  (1da7f95e / #65). Prefer a field of an existing record; a mutable `bool` flag adds a prism, a
  `usize` flag does not (d4428027 / #113). `vec![Vec::new(); n]` adds no prism, a loop building it
  does (1da7f95e).

## Proof style that held up

- **Opaque pre/post predicates** (`prop_pre`/`prop_post`): stated inline, `crush_base` split
  `propagate`'s contract into 44 goals (c3e0f79e).
- **Close `crush_base` goals with facts lemmas, `by (rule L)`**, whose assumptions are the goal's
  premises; never refer to `prems(n)` by position, never close many goals with one
  `by (fastforce …)+`: both break when `crush_base` changes its goals (d9396c62, 5952d953, 71bb750e).
  Name subgoal parameters by role; after a call added before a loop, name them with
  `apply (all ‹rename_tac …›)` (c2676fcb / #82).
- **State a bound in the form `crush_base` leaves.** It cancels common factors: for
  `fast * 7 > avg * 10` it needs `5 * unat (…) < 2^63`, and `unat (…) * 10 < 2^64` failed
  (2f71a521 / #104). Read the goal before writing the lemma. `vok_bound` gives `rvec_length v <
  2^57`, not `< 2^56` (fe122830).
- **The invariant `sok` in posts and invariants**: a premise `sok s` can instantiate the post's
  `sok ?s'` before the points-to is matched, leaving an unprovable `s = <new state>`. State
  preconditions and loop invariants with `sok_in` (`≡ sok`), and end a function with a call rather
  than a direct write after a call (67db04ed, 81673216).
- **rvec simplification gaps**: `crush_base` leaves `∇{rvec_elems_focus} f` inside record updates
  (use `rvec_elems_focus_modify_fun`); `auto` turns `∀w ∈ set (xs[k := y])` into a membership
  premise (use `in_set_update`); `node - c` without a bound becomes `(2^64 - c) + node` (use
  `node_norm`/`node_facts`) (81673216).
- **No-panic side goals go through the bound methods** `search_bound` (`Sat_Vectors`),
  `restart_bound` (`Sat_Reduce`), `cdcl_bound` (`Sat_CDCL`): add a word lemma as an alternative
  that closes its goal or fails (`; fail`), so the order does not matter (ae47ef21). Before removing
  an alternative, find which goals it closes (3b9d4646).
- **`rule L; (assumption | simp)`** handles the new subgoals last to first, so `simp` can fix a
  schematic bound before the assumption that should: write `rule L, assumption, assumption, simp,
  simp` (9f3404cc). `rule` does not unify `2^62` with its numeral; use a bridge lemma (3b9d4646).
- **Nested loops**: apply the inner `wp_bounded_while_framedI` after the outer one's `crush_base`,
  with only the references the inner body uses in its `INV`, and `BRK=‹λ_. ⟨False⟩›` for a loop
  without `break`; a loop directly inside an `else` branch failed, put it after the `if` (f381ca7f).
- **Keep theories under 1000 lines**: `Sat_Search` was split twice (`Sat_Reduce` #93,
  `Sat_Vectors` #105); `Sat_Proof` has 909, `Sat_Search` 810. Put new contracts in a new theory.
- **Review sessions**: count whole-word uses of each lemma in `proof/` and `spec/` and read every
  use site; unused lemmas are rare (one in #108, none in #122), the gains are wrappers, repeated
  steps turned into a method (`sok_asm`), and one-liners (15f18d1a, ae47ef21, fe122830, 1ff7d271).

## Design for verification

- **Untrusted search with checked answers.** CDCL needs no invariant of its search state: it only
  must not panic. `Sat` is checked by `satisfies`, each learned clause by `certify`, `Unsat` is a
  certified empty clause; on any failure the verified DPLL `solve` runs (adea3d20 / #45). Every
  search change since (#51–#120) kept it and needed only no-panic contracts (plus `sok`); keep it.
- **Lengths are checked where used, not related by invariants.** `len(x) == n` gives no `length` fact;
  under rvec, a length bounds the true length only with `rvec_wf` (`rvec_len_unat`), so a kept
  buffer needs `rvec_wf` in `sok` (adea3d20, 67db04ed, #113).
- **A fuel-bounded loop may stop early**: a loop whose full run soundness depends on (clearing a
  reused mark buffer) must be checked after it (`if k < len { fresh vector }`), not trusted (#113).
- **Checks may take untrusted hints.** `forced_sound` holds after forcing any variables in any
  order, so `certify` checks only the reasons analysis used (`Search.hint`): a wrong hint only fails
  the check, no proof about the hint is needed (d4428027 / #113, 1ff7d271 / #122). Look for this
  shape before proving a property of search data.
- **Tests of `solver` hardly reach the fallback** since CDCL runs first. Test `cdcl` and `dpll`
  directly against an independent oracle (5952d953, 7f86250c). Fuzzing and the suite catch search
  bugs the proofs (no panic only) cannot (1da7f95e).
- **The trusted `cli/` can give wrong answers**: a trailing lone `0` after the header's clauses was
  read as an empty clause, so pret was "UNSAT" without search and a satisfiable variant got a wrong
  answer (033a94e6 / #110). z3 `-dimacs` and `bench/check-model.py` read it the same way; strip it
  when comparing.

## Performance

- **Measure the ceiling before building.** Implicit binary watches: 1–2 % of visits (#78). Partial
  restarts: restarts undo ≤ 0.22 % of assignments on hole8/hole9, ceiling ≈ 0.2 % (#97). `cli/`
  parsing: ≈ 1.3 % of the small instances' time, while `bench/run.sh` itself is ≈ 74 % (7.7 ms per
  instance) (#100). Each of these closed as a negative result; count first, then decide.
- **Where the time is** (hole9, after #105): watch visits and `move_watch`/`scan` ~78 % of the
  instructions and most misses (67db04ed / #98); on uuf100/hole7 `propagate` 56–62 %, `analyze`
  17–22 %, `certify` 10 % (14.5 % of time) (#106). Profile by source line: callgrind
  `--dump-instr=yes` with `addr2line -i` attributes inlined code (f381ca7f, 67db04ed).
- **Separate a cheaper step from a luckier trajectory.** hole9 alone is luck-prone (minimisation:
  −38 % on hole9, −10 % on copies: 8468478b). Measure on 16 permuted copies of hole8 and hole9
  (variable renaming, polarity, clause and literal order) with conflict counts from an instrumented
  build: same conflicts ⇒ compare time per conflict; different ⇒ geometric mean of per-copy
  conflict ratios and summed user time. For small instances use an in-process harness (parse once,
  call `cdcl` repeatedly, min per formula), not `bench/run.sh` (#106, 20c72b96). The scripts are
  not in the repository; each session rewrites them (keep them out of the commit).
- **Tune on one set, accept on fresh seeds, and require hole8 not slower.** Tuning-set winners
  often fail: deletion `f700+700` −8.7 % on fresh hole9 but +5 % on hole8, not reproduced on seeds
  1–16, neighbours swinging both ways (#96); restart spacing `sp20` won on seeds 1–16, +3.2 % fresh;
  K = 0.7 lost on seeds 1–16 but won on all 176 fresh copies (00e71e54 / #104). Re-measure a tuned
  constant when the search around it changes (K 0.6 → 0.7 after #95; b0b18b19).
- **Standard constants are not a safe default here**: MiniSat/Glucose VSIDS decay (0.95) and every
  faster decay were worse on pigeon-hole; 0.998 gave −59 % on fresh hole9 (3a4b8b22 / #94). Measure
  both directions.
- **Compare variants in one binary**, selected by an environment variable, alternating per copy
  (order reversed on even seeds) in one session; the machine is loaded (load 5–50) and timings
  compare only within a run (c2676fcb, 5952d953, d4428027). Report `bench/run.sh` as min of 3
  alternating runs.
- **Read the assembly of the hot loop.** A loop that also stores reloads `Search` field pointers
  every node; a small read-only `&self` loop keeps them in registers (f381ca7f / #80). Keep a hot
  list in a local (`mem::replace`) (1da7f95e). Two call sites of `unit_lit` stopped inlining
  (c3e0f79e).
- **Gains came from fewer conflicts or fewer instructions per visit.** Fewer conflicts can still be
  slower (more live clauses): the "used" flag in `reduce` (+34 %, c2676fcb), deletion `i2000` and
  "keep 3/4" (#96); shorter learned clauses do not make a conflict cheaper (8468478b). Did not pay
  off — do not retry without a new reason:
  - blockers: MiniSat stale blocker, inline blocker (eda80d8c, 9f3404cc);
  - layout: `next`/`wkey` interleaved, newest-first visit, 3-word watch entries, dense key array,
    one cyclic scan, arena compaction (−3 %, #75), implicit binary watches (#78);
  - search: Luby restarts (41040648); partial restarts / trail reuse (#97); deletion schedule
    first interval, increment, kept fraction (#96); the LBD protection bound changes nothing on
    hole (the cut never reaches LBD ≤ 5, #96);
  - other: `lto = "fat"`/`codegen-units = 1` (c3e0f79e); branch-free `certify` conditions
    (d4428027); `cli/` parsing (#100).

## Coordination

- **Owner-approved work can be stranded.** The owner's decision on #98 said to continue the
  reason-side bumping of branch `agent/67fe3a00` (2f34b81: hole9 copies −43 to −62 %, suite
  1.78 → 1.16 s, measured on 7f17e8e) after the migration; #105 closed #98 without it, and no issue
  tracks it. When a PR closes an issue, check every deliverable and owner instruction landed, or
  file the rest as a new issue and name the branch.
- **Check for the same change in flight before implementing a lead.** #106's session built the
  certify hint while #113 was planned and merged as #116; PR #117 was closed as unsalvageable. Keep
  independent changes in separate commits: #117's second commit (992345c) was ported alone by
  cherry-pick as #119 (20c72b96), as #104's branch was after #105 (2f71a521).
- **When CI is blocked or a `spec/` change is needed**, keep measuring and leave the code on a
  branch with the remaining steps in the progress entry (#104); for the owner, write a report with
  the exact `spec/` diff, its size and a trial port (#102). The owner decided on that basis. One
  session's tool policy refused to write even the approved `spec/` diff; the next session's did not
  (67db04ed, 81673216): on a refusal, hand it back with `coordination needs-owner`.
