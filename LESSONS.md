# Lessons

Guidance distilled from repeated struggles and failed approaches in this repository, kept up to date
by lessons sessions (see `PLAN.md`). Read it before starting a task. Each lesson states what goes
wrong, what to do instead, and the evidence (progress entries, issues, pull requests); lessons that
no longer apply are removed. Progress entries are cited by session prefix (`progress/*_<prefix>.md`).

## Tooling: Pool Server and batch checks

- **The Pool Server is often unusable under load.** `isabelle_open` answers `busy`, HTTP 500 or
  `server_recovering` with no session of yours listed (c465b40d, b64c1dfb, d9396c62, 71bb750e).
  Retry once with a fresh `task_group` (e.g. the issue number); that worked where the default group
  failed (c3e0f79e, adea3d20). If it still fails, do not wait: develop with batch checks (below).
- **`isabelle_multi_attempt` rarely gets a scratch session** ("scratch pool exhausted" by other
  agents: c3e0f79e, adea3d20, 5952d953). Try steps by editing the file and re-checking in place.
- **Do not edit a file while the server is still checking it**: it produces spurious "Cannot join
  unrelated theory certificates" errors. Wait for the check to finish, or close and reopen
  (adea3d20). Editing a line above a `crush_base` that had finished gave the same error when it
  re-ran; and a changed imported theory (`urust/`, after regenerating) is not reloaded. In both
  cases `isabelle_close` with `destroy` and reopen (b0b18b19 / #85).
- **Large theories are slow in the Pool Server** (1700 lines: ~1 min per heavy step, ~25 min a pass).
  Check new contracts in a scratch theory in `dev/` holding only them and their dependencies
  (41040648), or batch-build only the new theory on a heap of the unchanged ones under `target/isa/`
  (1450 lines in 2.5 min against ~15 min sequentially: adea3d20).
- **`isabelle_build_heap` cannot build on AutoCorrode** ("Cannot load theory Micro_Rust_Std_Lib";
  it builds on HOL only). Open files without a heap (c3e0f79e, 41040648).
- **Batch-only recipe.** A ROOT session `= "AutoCorrode"` importing the one theory, with
  `quick_and_dirty` while developing, run time-bounded. End an unfinished step with `done` (not
  `sorry`): "Failed to finish proof" prints the remaining goals. `isabelle build_log -H Error
  <session>` shows every error with its full goal; `check.log` truncates them (b64c1dfb, adea3d20,
  71bb750e).
- **One hanging `metis`/`blast`/`auto` stalls a whole batch build** for its time limit; plain `auto`
  hangs on goals with large record-update premises. Prefer `rule`/`simp`-based structured steps
  (b64c1dfb, adea3d20).
- `coordination create-pr --help` is not help: it tries to create a PR (b64c1dfb).

## Writing code that `crush_base` can verify

AutoCorrode has issues disabled: report gaps on the project issue (as on #39, #34), and change the
code to avoid them. Known gaps and the workarounds that held:

- **Two mutable references from one call**: after a call whose contract returns two `&mut` results
  (or with two mutable `Vec<bool>` locals updated in turn), a points-to fact is lost. Give no
  function two `&mut` arguments; keep extra data as a field of the state record, use one helper with
  a single mutable local (b64c1dfb, adea3d20 gaps 1–2).
- **After a `&mut self` call the caller knows nothing of the state** (`∃ s'`): do the other writes
  first, call it last (41040648, `unlink`).
- **Large loop bodies**: `crush_base` took > 4 min on the whole CDCL loop body. Keep one loop per
  function; move branches into their own functions (`on_conflict`, `minimize`, `reduce`) (adea3d20
  gap 3, 41040648).
- **Sequential `if`s multiply `crush_base`'s paths**: a loop-free method with seven guarded
  updates in a row ran > 3 min; one block under a combined guard (`if a < X && b < Y { … }`) and
  one early `return` took ~1 min (b0b18b19, `restart_due`).
- **`loop` without `break`** translates to `panic!("unreachable …")` when fuel runs out; use
  `while cond` (e.g. `while steps < usize::MAX`) (adea3d20 gap 4).
- **`match` on an `Option` result is not split**: `cases x` and `simp only: option.case` before
  `crush_base` (adea3d20 gap 5).
- **A guarded update as a function's first statement** (`if t < NONE { t += 1 }`) duplicates the
  loop goal, so the loop proof block has to be repeated (41040648).
- **Avoid `continue`**; write an if/else chain (41040648).
- **Guards instead of relational invariants**: check `i < len` before `i += 1`, `v < x.len()` before
  an index, so no invariant relating lengths is needed (41040648, adea3d20).
- **A nested loop** (the copy loop inside the visit loop of `propagate_lit`) is provable: apply the
  inner `wp_bounded_while_framedI` after the outer one's `crush_base`, with only the references the
  inner body uses in its `INV`, and set `BRK=‹λ_. ⟨False⟩›` for a loop without `break`; left
  schematic, `crush_base` instantiated it with part of the state and the code after the inner loop
  lost its points-to facts. A loop directly inside an `else` branch also failed; put it after the
  `if` (f381ca7f / #80).
- **A call added before a loop shifts the loop's parameters**: its post (`∃ g' s'`) adds parameters
  in front, so `subgoal for n count_ref j_ref` binds the wrong ones (type clash `Search` vs
  `focused`). Name the loop's variables with `apply (all ‹rename_tac …›)`, which names the last
  parameters, as `learnt_lbd` does (c2676fcb / #82).
- **A new mutable local of a new type adds a prism** to the locale `Sat_heap` in `spec/`. Put such
  data in a field of an existing record when possible (41040648, the LBD histogram).

## Proof style that held up

- **Opaque pre/post predicates** (`prop_pre`/`prop_post`): stated inline, `crush_base` split
  `propagate`'s contract into 44 goals (c3e0f79e).
- **Close `crush_base` goals with facts lemmas, `by (rule L)`**, whose assumptions are the goal's
  premises; the closing `qed` discharges them by assumption, so their order and number do not
  matter. Duplicated goals share one step `apply (solves ‹rule L1 L2 …; assumption›)+`. Never refer
  to `prems(n)` by position, never close many goals with one `by (fastforce …)+`: both break when
  `crush_base` changes its goals (d9396c62 findings, 5952d953 / #50, 71bb750e / #52).
- **Name subgoal parameters by role** (`subgoal for pb c l r1`, not generated `x xa xb`)
  (d9396c62, 5952d953).
- **No-panic side goals** of the CDCL contracts are closed by one cleanup over word lemmas
  (`apply (all ‹(… | …)?›)`, adea3d20); it was copied six times, so define it once as an Eisbach
  method when touching it (review #48 in 71bb750e).
- **Keep theories under 1000 lines**; split code-independent lemmas off (`Sat_Partial`, #41) before
  a file grows past it (5952d953, 71bb750e: `Sat_CDCL` at 1415 lines).

## Design for verification

- **Untrusted search with checked answers.** CDCL needs no invariant of its search state: it only
  must not panic (indices checked, fuel-bounded `while`). `Sat` is checked by `satisfies`, each
  learned clause by `certify`, `Unsat` is a certified empty clause; on any failure the verified DPLL
  `solve` runs. This turned a 1450-line CDCL proof into no-panic goals plus two semantic checks
  (adea3d20 / #45). Keep it when the search changes (#51 added deletion without touching
  certification: 41040648).
- **No length relations between lists**: HOL lists may be longer than `2^64`, so `len(x) == n` does
  not give `length x = unat n`. Check bounds where they are used (adea3d20).
- **Tests of `solver` hardly reach the fallback** since CDCL runs first. Test `cdcl` directly and
  require an answer (`core/tests/cdcl.rs`); compare with an independent oracle, not with `solver`
  (5952d953, 71bb750e / #52).

## Performance

- **Measure before optimising.** Certification was under 5 % of the time; the cost was propagation
  over an ever-growing clause database (41040648 / #51). On DPLL, constant factors could not bring
  uuf50 under the limit; the algorithm had to change (c465b40d).
- **Check inlining.** Two call sites of `unit_lit` made a faster algorithm slower (5.6 s vs 3.1 s)
  because LLVM did not inline; one call site fixed it. `lto = "fat"` / `codegen-units = 1` were
  slower (c3e0f79e / #44).
- **Tune on permuted copies** (variable renaming, clause and literal order), not on one instance
  only; several variants were "worse or noisier" there. Luby restarts were worse than geometric
  ones (41040648).
- **Read the assembly of the hot loop.** Inlined into `cdcl`, the fields of `Search` live in memory:
  a loop that also stores (into the watch list) reloads the `arena`/`false_lit` pointers and
  lengths for every node. A small read-only `&self` loop (`skip_true`) keeps them in registers: −6 %
  on the hole9 copies at the same trajectory, with the same cache misses. Write a select of an index
  as arithmetic (`o + 5 - side`) when it must not become a branch (f381ca7f / #80).
- **The machine is loaded** (load average 10–38): instances near the 20 s limit can go either way,
  and timings compare only within one run (c465b40d, c3e0f79e, 5952d953).
