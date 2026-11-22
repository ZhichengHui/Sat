# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed. Progress entries are cited by session prefix (`progress/*_<prefix>.md`).

## Tooling: Pool Server and batch checks

- **The Pool Server is often unusable.** `isabelle_open` answers `busy`, HTTP 500 or
  `server_recovering` (c465b40d, b64c1dfb, 3b9d4646, 7f86250c, 15f18d1a, f381ca7f). Retry once with
  a fresh `task_group` (the issue number); that worked in c3e0f79e, adea3d20, 8468478b, f381ca7f.
  It does not always: `dev/Sat_Minimize.thy` gave "Bad theory name" in both groups, and
  `dev/Sat_Search.thy` took minutes per old step and then errored (c2676fcb / #82). Do not spend
  the session on it: fall back to batch checks (below).
- **`isabelle-check` alone is a workable loop** (~8.5–10 min a pass); 7f86250c, 15f18d1a and
  c2676fcb developed and verified their proofs with it only. Batch several fixes per pass.
- **Faster batch passes**: a task heap of the unchanged theories (up to `Sat_Search`: 4.5 min to
  build) and a session with only the changed theory on it (3b9d4646; 1450 lines in 2.5 min instead
  of ~15: adea3d20). `isabelle_build_heap` cannot build on AutoCorrode ("Cannot load theory
  Micro_Rust_Std_Lib"); build the heap with `isabelle build` and a ROOT entry, delete it afterwards.
- **Batch-only recipe.** End an unfinished step with `done` (not `sorry`): "Failed to finish proof"
  prints the remaining goals. `isabelle build_log -H Error <session>` shows every error with its
  full goal; `check.log` truncates them (b64c1dfb, adea3d20, 71bb750e).
- **Stale state in the Pool Server.** It keeps the imported theories it loaded at `isabelle_open`:
  after regenerating `urust/` and `isabelle-devcopy`, close and reopen the file (1da7f95e). Editing
  a file while it is being checked gives spurious "Cannot join unrelated theory certificates";
  wait for the check, or close and reopen (adea3d20, 9f3404cc). Editing a line above a finished
  `crush_base` gave the same error when it re-ran: `isabelle_close` with `destroy`, then reopen
  (b0b18b19 / #85).
- **`isabelle_multi_attempt` rarely gets a scratch session** ("scratch pool exhausted": c3e0f79e,
  adea3d20, 5952d953). Try steps by editing the file and re-checking in place.
- **One hanging `metis`/`blast`/`auto` stalls a whole batch build** for its time limit; plain `auto`
  hangs on goals with large record-update premises. Prefer `rule`/`simp` steps (b64c1dfb, adea3d20).
- `coordination create-pr --help` is not help: it tries to create a PR (b64c1dfb).

## Writing code that `crush_base` can verify

AutoCorrode has issues disabled: report gaps on the project issue (as on #39, #34), and change the
code to avoid them. Known gaps and the workarounds that held:

- **Two mutable references from one call**: after a call whose contract returns two `&mut` results
  (or with two mutable `Vec<bool>` locals updated in turn), a points-to fact is lost. Give no
  function two `&mut` arguments; keep extra data as a field of the state record (b64c1dfb,
  adea3d20 gaps 1–2).
- **After a `&mut self` call the caller knows only what its contract says** (`∃ s'`): do the other
  writes first and the call last (41040648), and re-check a bound the code needs after the call
  when the callee's contract does not keep it (`lbd` after `clause_lbd`: c2676fcb / #82).
- **Large loop bodies are slow**: `crush_base` took > 4 min on the CDCL loop body (adea3d20) and
  on the first arena visit with the watch move inside the loop (9f3404cc / #71). One loop per
  function; move slow paths into their own functions (`on_conflict`, `move_watch`,
  `redundant_step`). Inside a big body write offsets as `if side == 0 { o + 5 } else { o + 4 }`;
  arithmetic like `o + 5 - side` is fine in a small function with a lemma (`other_key`,
  `side_ix`), and in Rust an `if side` select can become a branch (+15 %: f381ca7f / #80).
- **Sequential `if`s multiply `crush_base`'s paths**: seven guarded updates in a row ran > 3 min;
  one block under a combined guard (`if a < X && b < Y { … }`) took ~1 min (b0b18b19, `restart_due`).
- **`loop` without `break`** translates to `panic!("unreachable …")` when fuel runs out; use
  `while cond` (e.g. `while steps < usize::MAX`) (adea3d20 gap 4). **Avoid `continue`**; write an
  if/else chain (41040648).
- **`match` on an `Option` result is not split**: `cases x` and `simp only: option.case` before
  `crush_base` (adea3d20 gap 5).
- **A guarded update as a function's first statement** (`if t < NONE { t += 1 }`) duplicates the
  loop goal, so the loop proof block has to be repeated (41040648).
- **Guards instead of relational invariants**: check `i < len` before `i += 1`, `v < x.len()` before
  an index, so no invariant relating lengths is needed (41040648, adea3d20, 1da7f95e, 9f3404cc).
- **Nested loops** (the copy loop of `propagate_lit`): apply the inner
  `wp_bounded_while_framedI` after the outer one's `crush_base`, with only the references the inner
  body uses in its `INV`, and set `BRK=‹λ_. ⟨False⟩›` for a loop without `break`; left schematic,
  it took part of the state and later code lost its points-to facts. A loop directly inside an
  `else` branch also failed; put it after the `if` (f381ca7f / #80).
- **A call added before a loop shifts the loop's parameters** (its post adds `∃ g' s'` in front):
  `subgoal for …` binds the wrong ones. Name them with `apply (all ‹rename_tac …›)`, which names
  the last parameters (`learnt_lbd`, `analyze_clause`: c2676fcb / #82).
- **A new mutable local of a new type adds a prism** to the locale `Sat_heap` in `spec/`: then
  update the locale, the prism list of `solver`, and `Sat_ctxI` in `proof/top/Sat_Top.thy`, which
  lists the prisms (1da7f95e / #65). Prefer a field of an existing record (41040648);
  `vec![Vec::new(); n]` adds no prism for the outer vector, a loop building it does (1da7f95e).

## Proof style that held up

- **Opaque pre/post predicates** (`prop_pre`/`prop_post`): stated inline, `crush_base` split
  `propagate`'s contract into 44 goals (c3e0f79e).
- **Close `crush_base` goals with facts lemmas, `by (rule L)`**, whose assumptions are the goal's
  premises; never refer to `prems(n)` by position, never close many goals with one
  `by (fastforce …)+`: both break when `crush_base` changes its goals (d9396c62, 5952d953 / #50,
  71bb750e / #52). Name subgoal parameters by role (`subgoal for pb c l r1`).
- **No-panic side goals go through the bound methods** `search_bound`, `restart_bound`
  (`Sat_Search`) and `cdcl_bound` (`Sat_CDCL`): add a word lemma as an alternative that closes its goal or fails
  (`; fail`), so the order does not matter (ae47ef21 / #76). Before removing an alternative, find
  which goals it closes (an ML method that prints, per goal, the alternatives that close it):
  dropping one left a goal of `cdcl_spec` open (3b9d4646 / #63).
- **`rule L; (assumption | simp)`** handles the new subgoals last to first, so `simp` can fix a
  schematic bound before the assumption that should fix it: write `rule L, assumption, assumption,
  simp, simp` (9f3404cc / #71). `rule` does not unify `2^62` with its numeral; a bridge lemma
  (`learned_push'`) is needed (3b9d4646).
- **Keep theories under 1000 lines** (split as `Sat_Minimize` was: 8468478b / #74). `Sat_Search`
  has 1041 since #86: put new contracts in a new theory added to `ROOT`, or split it first.
- **Review sessions**: count whole-word uses of each lemma in `proof/` and `spec/` and read every
  use site; unused lemmas are rare, the gains are wrappers and duplicated conclusions (15f18d1a,
  ae47ef21).

## Design for verification

- **Untrusted search with checked answers.** CDCL needs no invariant of its search state: it only
  must not panic (indices checked, fuel-bounded `while`). `Sat` is checked by `satisfies`, each
  learned clause by `certify`, `Unsat` is a certified empty clause; on any failure the verified DPLL
  `solve` runs (adea3d20 / #45). Every search change since (#51–#86) kept it and needed only
  no-panic contracts; keep it.
- **No length relations between lists**: HOL lists may be longer than `2^64`, so `len(x) == n` does
  not give `length x = unat n`. Check bounds where they are used (adea3d20).
- **A fuel-bounded loop may stop early**: a loop whose full run soundness depends on (clearing a
  reused mark buffer) must be checked after it (`if k < len { fresh vector }`), not trusted; and
  `rvec_wf v` gives `unat (word64_of_nat (rvec_length v)) = rvec_length v` (`rvec_len_unat`), so
  keep `rvec_wf` of a kept buffer in `sok` (#113).
- **Checks may take untrusted hints.** `forced_sound` holds after forcing any variables in any
  order, so `certify` checks only the reasons analysis used (`Search.hint`); a wrong hint only fails
  the check. To lend a `Search` field to a checker, make it a `Search` method that takes the field
  with `mem::replace` and stores it back, not a free function with `&mut s.field` (#113).
- **Tests of `solver` hardly reach the fallback** since CDCL runs first. Test `cdcl` and `dpll`
  directly and compare with an independent oracle, not with `solver` (5952d953, 7f86250c / #69).
  Fuzzing and the suite catch search bugs that the proofs (no panic only) cannot: a truncation bug
  made hole9 time out (1da7f95e).

## Performance

- **Measure before implementing, and gate on it.** #78 counted binary-clause watch visits first:
  1–2 % of visits, so implicit binary watches were not built (issue #78). Certification was under
  5 % (41040648, f381ca7f); propagation dominates: the watch visit and scan are ~60 % of the
  instructions, conflict analysis ~5 % (eda80d8c, 9f3404cc, f381ca7f).
- **Separate a cheaper step from a luckier trajectory.** hole9 alone is luck-prone: minimisation
  gave −38 % on hole9 but −10 % on its copies, and hole8 +31 % against −7.5 % on its copies
  (8468478b / #74). Measure on ≥ 16 permuted copies of hole8 and hole9 (variable renaming,
  polarity, clause and literal order) with conflict counts from an instrumented build: same
  conflict counts ⇒ compare µs per conflict; different ⇒ geometric mean of per-copy conflict ratios
  and summed user time. Neither the permutation script nor the counters are in the repository;
  each session rewrote them (keep them outside the commit).
- **Compare variants in one binary**, selected by an environment variable, in alternating runs in
  one session; the machine is loaded (load 5–40) and timings compare only within a run (c2676fcb,
  c465b40d, 5952d953). Report `bench/run.sh` as min of 3 alternating runs.
- **Profile by source line**: everything is inlined into `cdcl`, so callgrind/cachegrind with
  debug info attributed per line is what locates the cost (f381ca7f). Instruction count decided
  speed at first (eda80d8c); after the arena, D1 misses and mispredicts cost about as much
  (9f3404cc).
- **Read the assembly of the hot loop.** Fields of `Search` live in memory: a loop that also stores
  reloads the `arena`/`false_lit` pointers every node; a small read-only `&self` loop
  (`skip_true`) keeps them in registers (−6 %, f381ca7f / #80). Keep a hot list in a local
  (`mem::replace`) instead of indexing `self.watches[k]` in the loop (1da7f95e / #65). Two call
  sites of `unit_lit` stopped inlining and made it slower (c3e0f79e / #44).
- **Gains came from fewer conflicts or fewer instructions per visit, not from memory layout
  alone.** Did not pay off — do not retry without a new reason:
  - stale blockers: MiniSat blocker 51 → 71 µs per conflict (eda80d8c); inline blocker of #67
    attempt C changed the trajectory, no cheaper per conflict (9f3404cc);
  - layout: `next`/`wkey` interleaved (eda80d8c); newest-first visit (1da7f95e); an exact copy of
    the other watched key in 3-word watch entries, a dense per-clause key array (+3 %), one
    cyclic scan (f381ca7f); arena compaction after `reduce`, −3 % only, from L3 fit (issue #75);
    implicit binary watches (issue #78, above);
  - search: a "used" flag sparing clauses in `reduce`, +34 % time (more live clauses, 28.6 → 46 µs
    per conflict) despite fewer conflicts (c2676fcb / #82); Luby restarts (41040648);
    `lto = "fat"`/`codegen-units = 1` (c3e0f79e).
- **Shorter learned clauses do not make a conflict cheaper** (watch visits dominate); minimisation
  and LBD gains come from fewer conflicts (8468478b, c2676fcb).
- **Validate tuned parameters on fresh copies.** Glucose restarts with K = 0.8 gave hole9 copies
  a conflict ratio of 1.10 (+41 % time) on one set (before #83), 0.92 on a fresh set after it;
  K = 0.6 was confirmed on the fresh set, not on the suite (b0b18b19 / #85). Re-measure a tuned
  constant when the search around it changes.
