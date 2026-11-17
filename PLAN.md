# Plan

Written by the owner of this repository. Agents follow it and never edit it.

## Direction

Work is directed by the owner through GitHub issues. There is no autonomous roadmap: planners do
not invent work.

- An issue labelled `agent-plan` is a work item; a worker claims and does it.
- An issue labelled `directive` is a larger task from the owner; a planner splits it into
  `agent-plan` issues (or a worker does it directly when it is small), and closes it when its
  deliverables are merged.
- When there is no open `directive` and no unclaimed `agent-plan` issue, planners create no issues
  and signal `return-to-human`.

## Rules

### The specification

- `spec/` is the specification: the meaning of the top-level theorem `Sat_heap.solver_correct`
  depends on nothing else.
- `spec/` is fixed, with one exception: the locale `Sat_heap` in `spec/Sat_Spec.thy` is the
  generated locale `Sat_ctx` of `urust/Sat_Locale.thy` without its fuel line. When the
  implementation uses a new type of mutable local, the generated locale gains a parameter, and
  `Sat_heap` is updated to match it exactly. Nothing else in `spec/` changes unless the owner
  changes it.
- `tools/check-spec.sh` enforces this in CI: outside the locale `Sat_heap`, `spec/` must match the
  manifest `tools/spec.sha256`, and the locale must match the generated one. Only the owner
  updates the manifest (`tools/check-spec.sh --update`).
- Make the solver fit the specification, never the specification fit the solver.

### Verified code

- Every change keeps every proof and the statement of `solver_correct`, and leaves no `sorry`,
  `oops` or `quick_and_dirty` in `spec/` or `proof/`.
- Do not weaken a contract or a lemma used by the top level to make a proof easier; do not delete a
  proved lemma that is still used.
- Every pull request passes CI: the check of `spec/`, `cargo test`, and every proof.

### Trusted base

Not proved in this repository, and not to be presented as proved: the AutoCorrode translation, the
assumptions of the locale `Sat_heap` (AutoCorrode's reference model), and the command line `cli/`
(DIMACS input, output of the answer).
