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
  sessions verified with `isabelle-check` alone (2f71a521, fe122830, d4428027, 20c72b96,
  18071633, c777cec3 / #154). It checked the small `Sat_Heap` fine but sat in `Sat_Search`'s slow
  proofs (049e0cc5).
- **`isabelle-check` is a workable loop**: ≈ 7–8 min a pass since #140 (049e0cc5, 624009c9,
  664a38a6, c777cec3 / #154), 16–17 min before. Batch several fixes per pass.
- **Faster batch passes**: copy `urust/`, `spec/`, `proof/` to an untracked directory, rename the
  sessions with the task (`Sat_t145`, `SatSearch_t145` = `Sat_Partial` … `Sat_Search`), rewrite the
  qualified imports with `sed`, build the unchanged theories as task heaps with `isabelle build`,
  and put the edited theory alone in a last session: ≈ 2 min a pass for `Sat_Minimize` (68d99558;
  earlier 9d635ebd, 81673216, adea3d20). Two sessions cannot share a directory in one ROOT: give
  each its own. `isabelle_build_heap` cannot build these heaps ("Cannot load theory
  Micro_Rust_Std_Lib"; refused since `Sat_Partial` has an `ML` command: d4428027). Delete the
  heaps afterwards. `isabelle-check` ignores the options of `proof/ROOT` (it builds one task session).
- **Batch-only recipe.** End an unfinished step with `done` (not `sorry`): "Failed to finish proof"
  prints the remaining goals. `isabelle build_log -H Error <session>` shows every error with its
  full goal; `check.log` truncates them (b64c1dfb, adea3d20). Watch the log for "running for"
  > 180 s (81673216).
- **Many proof variants in one batch pass.** To find which steps of a proof can go, add
  temporary copies of the lemma with different proofs and new names (`..._spec_t1`, …) next to
  it. Nothing uses the copies, and one pass reports every failing copy by line. 12 variants of
  two contracts took one 17-minute pass, and a second pass checked the combination (18071633).
  Single removals that pass alone can still fail together (again in c777cec3 / #154). Generate the
  variants with a script from a kept clean copy (43 variants of six contracts in four passes);
  splitting lemmas by regex loses those with a nested `subgoal … done` (c777cec3). Delete the
  copies before the final pass.
- **Find where proof time goes before changing proofs.** Per command: the session database holds
  every command ≥ 0.1 s; `Store.read_command_timings` with `Properties.uncompress` from an
  `isabelle scala` script prints them with symbol offsets, mapped to lines (9d635ebd, 68d99558).
  Per goal: a method `trace_all` (Eisbach's `all`, timing the method on each goal and appending
  `label #i time SOLVED/LEFT/FAIL` to a file) in an instrumented copy; warnings in the build
  database were not reliable for this (9d635ebd).
- **Stale state in the Pool Server.** It keeps the imported theories it loaded at `isabelle_open`:
  after regenerating `urust/` and `isabelle-devcopy`, close and reopen the file (1da7f95e). Editing
  a file while it is being checked, or a line above a finished `crush_base`, gives spurious "Cannot
  join unrelated theory certificates": wait, or `isabelle_close` with `destroy` and reopen
  (adea3d20, 9f3404cc, b0b18b19).
- **`isabelle_multi_attempt` rarely gets a scratch session** ("scratch pool exhausted": c3e0f79e,
  adea3d20, fe122830). Try steps by editing the file and re-checking in place.
- **One hanging `metis`/`blast`/`auto` stalls a whole batch build** for its time limit (plain
  `auto` on large record-update premises; `sok_tac` > 5 min on `cdcl`'s loop): prefer `rule`/`simp`
  steps and targeted lemmas, see "cascade" below (b64c1dfb, adea3d20, 81673216).
- **A proof that fails only in CI with "Cannot transfer: not a super theory"** was a timing race
  between forked proofs on the slower runners, not a wrong proof; `proof/ROOT` now sets
  `parallel_proofs = 0` for `Sat_Proof` (53f8b137 / #92). The `ML` warm-up of `Sat_Partial` removed
  the race: #135 dropped the option again (3/3 CI runs green, `Sat_Proof` 18:49 → 9–14 min). If
  "Cannot transfer" comes back, extend the warm-up before going sequential again.
- **CI runner speed varies by ±30 %** between runs (AutoCorrode 6:44–11:24 on the same sources):
  compare session times as ratios to an untouched session in the same run (#135).
- **Killing processes**: a script that computed a kill list (awk over `ps`) sent SIGTERM to ~390
  processes of the user, among them Pool Server sessions and other agents' work (67db04ed / #98).
  List the children with `ps --ppid` and kill named PIDs only.
- **`coordination … --help` is not help**: `coordination plan --help` posted an issue titled
  `--help` four times (#128, #130, #147, #152); `create-pr --help` tries to create a PR (b64c1dfb).
  Read the command table of the `agent-worker-flow` skill instead.

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
- **Loop shapes that break the loop proof**: an `if c { self.call() }` before a loop doubles the
  loop goals (handle them with `apply (all ‹ucincl_discharge…›)`, 049e0cc5 / #144); an early
  `return` before a loop changes the goal's parameters, so `subgoal for i_ref` fails. Put the loop
  in its own function (`close_hint`) and keep early returns in loop-free functions (624009c9 /
  #149).
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
  first check, grep `proof/` for the old constant (3a4b8b22, 2f71a521). A `const` used in an
  expression must be inlined for `crush_base` (`inline: BIG_def`, `HEAP_MIN_def`: 049e0cc5).
- **A new mutable local of a new type adds a prism** to the locale `Sat_heap` in `spec/`: then
  update the locale, the prism list of `solver`, and `Sat_ctxI` in `proof/top/Sat_Top.thy`
  (1da7f95e / #65). Prefer a field of an existing record; a mutable `bool` flag adds a prism, a
  `usize` flag does not (d4428027 / #113). `vec![Vec::new(); n]` adds no prism, a loop building it
  does (1da7f95e). A new vector of fixed length `n` with guarded indices leaves `sok` unchanged
  (the heap of #144); one that grows needs a `vok` conjunct in `sok` (`hint0`, #149).

## Proof style that held up

- **In a `(m; fail)?` cascade over all goals, put the cheap specific steps first.** The cost is
  mostly the failures and the goals a later cheaper step would close: `sok_tac` (an `auto`) took
  25 s on goals `sok_lbd_dead` closes, and `cdcl_bound` failed 1–2 s on each of 50–85 `sok` goals.
  Running `sok_asm` and `rule L; assumption` steps first took `Sat_Proof` from 931 s to 350 s
  elapsed (9d635ebd / #140); the rule-based `sok_fast` (`sok_frame`, `sok_elems`, `sok_push`)
  cut `Sat_Minimize`'s cascades from ≈ 95 s to 7 s (68d99558 / #146). Write new cascades as
  `(sok_fast; fail)?`, `search_bound?`, `(sok_tac; fail)?`; for a new vector in `sok`, add its
  facts to `sok_elems`/`sok_push` instead of a new method (c777cec3 / #154). Broad `auto` on word
  bounds took 4–35 s each: use `rule word64_less_of_nat word64_less_max, assumption` (9d635ebd).
  What remains is `crush_base` itself (68d99558).
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
  `Sat_Vectors` #105); `Sat_Proof` has 909, `Sat_Search` 785. New contracts went into new theories
  (`Sat_Heap` #144, `Sat_Level0` #149); keep doing that.
- **Review sessions**: count whole-word uses of each lemma in `proof/` and `spec/` and read every
  use site; unused lemmas are rare (one in #108, none in #122, #137, #151), the gains are template
  steps that do nothing (#137, #154), repeated step blocks turned into a method (`sok_asm`,
  `heap_crush` #151, `sok0` folded into `sok_fast` #154), and one-liners (15f18d1a, ae47ef21,
  1ff7d271, 18071633, 664a38a6, c777cec3).

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
  the check, no proof about the hint is needed (d4428027 / #113, 1ff7d271 / #122; `hint0`, the
  level-0 reasons in DFS post-order: 624009c9 / #149). Look for this shape before proving a
  property of search data. Its limit: work that must be *trusted* to be complete, such as clearing
  only the marks an untrusted list names, cannot be checked cheaply and would need an invariant
  on the marks in `sok` (624009c9).
- **Tests of `solver` hardly reach the fallback** since CDCL runs first. Test `cdcl` and `dpll`
  directly against an independent oracle (5952d953, 7f86250c). Fuzzing and the suite catch search
  bugs the proofs (no panic only) cannot (1da7f95e).
- **The trusted `cli/` can give wrong answers**: a trailing lone `0` after the header's clauses was
  read as an empty clause, so pret was "UNSAT" without search and a satisfiable variant got a wrong
  answer (033a94e6 / #110). z3 `-dimacs` and `bench/check-model.py` read it the same way; strip it
  when comparing. z3 omits don't-care variables from its models (305 models in #141), which
  `bench/check-model.py` rejects: check z3's models leniently, ours strictly (4da8f4f8).

## Performance

- **Measure the ceiling before building.** Implicit binary watches: 1–2 % of visits (#78). Partial
  restarts: restarts undo ≤ 0.22 % of assignments on hole8/hole9, ceiling ≈ 0.2 % (#97). `cli/`
  parsing: ≈ 1.3 % of the small instances' time, while `bench/run.sh` itself is ≈ 74 % (7.7 ms per
  instance) (#100). Each of these closed as a negative result; count first, then decide.
- **Where the time is**: propagation ≈ 72 % on hole9, 58 % on uuf100 ×10 + hole7, then `analyze`
  10–13 % (e406fb4c). On bmc the linear `pick` (24–58 %, heap #144) and then `certify`'s level-0
  prefix (46 % of galileo-9, #149) dominated; now propagation is 71 % there (049e0cc5, 624009c9).
  Profile by source line: callgrind `--dump-instr=yes` with `addr2line -i` attributes inlined
  code (the PIE's addresses are file offsets: 624009c9; f381ca7f, 67db04ed).
- **The tuning families do not cover structured instances.** Against z3 we lose most on bmc
  (58.8 s vs 6.1 s) and hanoi5 (25.3 s vs 7.6 s), win on hole10 and uf/uuf225–250 (4da8f4f8 /
  #141). Changes tuned on hole/uuf100 need a bmc/hanoi run, and wins on bmc must keep the small
  guards (below).
- **A change that pays on large instances can cost 3–5 % on small ones**: gate it by a cost
  comparison, not by hope. The heap for `pick` was 3–5 % slower on uuf100/hole, so it runs from
  `HEAP_MIN = 512` variables (049e0cc5 / #144); the level-0 DFS lost ≈ 3 % on hole, where the
  prefix is one variable, so it runs only if `lim[0] > hint.len()`, a rule with no tuned constant
  (624009c9 / #149). An untrusted hint must not cost more than the check it replaces.
- **A pure speed change should keep the trajectory**: check byte-identical output to main on the
  suite, the copies and bmc/hanoi with the new path forced on (049e0cc5 / #144, 624009c9 / #149).
- **Separate a cheaper step from a luckier trajectory.** hole9 alone is luck-prone (minimisation:
  −38 % on hole9, −10 % on copies: 8468478b). Measure on 16 permuted copies of hole8 and hole9
  (variable renaming, polarity, clause and literal order) with conflict counts from an instrumented
  build: same conflicts ⇒ compare time per conflict; different ⇒ geometric mean of per-copy
  conflict ratios and summed user time. For small instances use an in-process harness (parse once,
  call `cdcl` repeatedly, min per formula), not `bench/run.sh` (#106, 20c72b96). A 16-copy
  geometric mean of conflicts on hole is good to only ±14 % (2σ): decide close calls on 64 copies
  (e406fb4c / #138). The suite's hole9 went 0.44 → 0.13 s by luck in #132 and back to 0.28 s in
  #138 while every copy set improved (e406fb4c). The scripts are not in the repository; each
  session rewrites them (keep them out of the commit and the worktree).
- **Gate an adaptive heuristic on a signal that separates the families from the start.** Reason
  bumping paid on hole (LBD 7–15) and cost uuf100 (LBD 4–5) +32 % (4c0e068b / #129); a per-clause
  length limit (CaDiCaL's direction) did not separate them, the average LBD did (357d9a1f / #132),
  but the cumulative average starts at `0 ≥ 0` and is ruled by the first noisy conflicts; the fast
  moving average (starts at 0) fixed uuf100 (18071633, e406fb4c / #138).
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
- **Read the assembly of the hot loop, and count instructions before timing.** A loop that also
  stores reloads `Search` field pointers every node; a small read-only `&self` loop keeps them in
  registers (f381ca7f / #80). Keep a hot list in a local (`mem::replace`) (1da7f95e). Two call
  sites of `unit_lit` stopped inlining (c3e0f79e). A never-executed branch whose callee got
  inlined cost +1.4 % instructions in `cdcl` on hole9; `#[inline(never)]` on the cold functions
  made it −0.1 % (the front end ignores the attribute) (049e0cc5 / #144). Callgrind counts are
  deterministic and show 0.1–2 % effects timings cannot; a review that changes such code needs
  this measurement (664a38a6).
- **Gains came from fewer conflicts or fewer instructions per visit.** Fewer conflicts can still be
  slower (more live clauses): the "used" flag in `reduce` (+34 %, c2676fcb), deletion `i2000` and
  "keep 3/4" (#96); shorter learned clauses do not make a conflict cheaper (8468478b). Did not pay
  off — do not retry without a new reason:
  - blockers: MiniSat stale blocker, inline blocker (eda80d8c, 9f3404cc);
  - layout: `next`/`wkey` interleaved, newest-first visit, 3-word watch entries, dense key array,
    one cyclic scan, arena compaction (−3 %, #75), implicit binary watches (#78);
  - search: Luby restarts (41040648); partial restarts / trail reuse (#97); deletion schedule
    first interval, increment, kept fraction (#96); the LBD protection bound changes nothing on
    hole (the cut never reaches LBD ≤ 5, #96); always-on reason bumping (#129); bumping each
    reason variable at most once per conflict (hole9 conflicts ×2.05) and `fast` thresholds other
    than 6.5 (e406fb4c);
  - other: `lto = "fat"`/`codegen-units = 1` (c3e0f79e); branch-free `certify` conditions
    (d4428027); `cli/` parsing (#100).

## Coordination

- **Owner-approved work can be stranded.** The owner's decision on #98 said to continue the
  reason-side bumping of branch `agent/67fe3a00` after the migration; #105 closed #98 without it,
  and only a lessons session noticed (b5b7b776); it landed as #129/#132. When a PR closes an
  issue, check every deliverable and owner instruction landed, or file the rest as a new issue
  and name the branch. A negative result keeps its port on a named branch so the next issue can
  build on it (`agent/4c0e068b`: #129 → #132).
- **Check for the same change in flight before implementing a lead.** #106's session built the
  certify hint while #113 was planned and merged as #116; PR #117 was closed as unsalvageable. Keep
  independent changes in separate commits: #117's second commit (992345c) was ported alone by
  cherry-pick as #119 (20c72b96), as #104's branch was after #105 (2f71a521).
- **When CI is blocked or a `spec/` change is needed**, keep measuring and leave the code on a
  branch with the remaining steps in the progress entry (#104); for the owner, write a report with
  the exact `spec/` diff, its size and a trial port (#102). The owner decided on that basis. One
  session's tool policy refused to write even the approved `spec/` diff; the next session's did not
  (67db04ed, 81673216): on a refusal, hand it back with `coordination needs-owner`.
