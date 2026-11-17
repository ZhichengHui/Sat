# Plan

Written by the owner of this repository. Agents follow it and never edit it.

## Direction

The solver is verified; that is the start, not the finish. The proofs are a ratchet: they make
aggressive improvement safe, as long as they hold at every commit. Proof churn is the expected cost
of an improvement, not a reason to avoid one; never route a change around the proofs.

- Make the solver faster while every proof holds. The present solver enumerates all assignments;
  the way forward is the standard one: unit propagation, then DPLL, then conflict-driven clause
  learning, each step verified against the unchanged `solver_correct`.
- Issues from the owner come first. An issue labelled `agent-plan` is a work item; a worker claims
  and does it. An issue labelled `directive` is a larger task; a planner splits it into `agent-plan`
  issues (or a worker does it directly when it is small), and closes it when its deliverables are
  merged.
- When no owner's issue is waiting and a benchmark suite is active, planners take the next steps
  of the goal above, aimed at the active suites: small `agent-plan` issues, each with an aim
  measurable on them, ordered so that each builds on merged work. When no owner's issue is waiting
  and no suite is active, planners create no issues and signal `return-to-human`.

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

### The verification framework

- The Rust code is verified with our own AutoCorrode framework: the front end
  `ZhichengHui/AutoCorrodeRustFrontEnd` (Rust to Isabelle) and the Isabelle library
  `ZhichengHui/AutoCorrode`. Both are installed in the agents' environment on the compute server.
- The framework supports a subset of Rust, and not yet all of it. Write the code in that subset:
  the translation has no placeholders (`urust/PLACEHOLDERS.txt` reports 0) and no new stubs of
  external functions in `urust/*_Template.thy`.
- When a construct you need is not supported, rewrite the code with supported constructs that do
  the same. Stop the task (and say why on its issue) only when no reasonable rewrite exists.
- Report every gap you meet to the framework, also the ones you worked around: an issue in its
  repository (the front end for what does not translate, AutoCorrode for what its library or
  automation lacks), labelled `from-agent`, with a minimal Rust example, what the translation
  produced, and the workaround you took, if any; link it from the issue of your task. The owner,
  or agents working on the framework, improve it from these issues.
- The framework is always the newest commit of its main branches: the agents' launcher updates the
  front end and AutoCorrode (rebuilding its heap) before every start, and CI checks out both at
  their newest commit.

### Verified code

- Every change keeps every proof and the statement of `solver_correct`, and leaves no `sorry`,
  `oops` or `quick_and_dirty` in `spec/` or `proof/`.
- Do not weaken a contract or a lemma used by the top level to make a proof easier; do not delete a
  proved lemma that is still used.
- Every pull request passes CI: the check of `spec/`, `cargo test`, and every proof.

### Tests

- Tests are auxiliary and secondary: the proofs establish correctness. The test infrastructure
  (`core/tests/`, `tools/fuzz.py` against z3) is a quick way to find a likely bug before the slow
  proof work.
- Meaningful tests may be added, such as a case that once exposed a bug. No change requires a
  test, and a failing test means a bug in the code or in the test.

### Benchmarks

- Progress of the Direction is judged by the active benchmark suites. A pull request that aims to
  improve the solver runs the active suites and reports the results against main.
- A suite is a directory `bench/SUITE/` with a `suite.sh` that `bench/run.sh` reads: what it
  measures, its instances with their source and known answers, the time and memory limit per
  instance, and how answers (and, where possible, models) are checked. Instances that are not
  small are fetched from their public source and checked by hash, not committed. The agent that
  builds the first suite also writes `bench/run.sh`.
- `bench/active` lists the active suites, one per line. The owner activates and deactivates them;
  an inactive suite stays in `bench/` and is not run.
- Suites are built only for issues of the owner. A suite takes instances with known answers from
  public collections (SATLIB, or SAT-COMP through GBD), some that the solver solves and some that it does not yet,
  graded in difficulty where possible. Its pull request states what it measures, why it is at the
  frontier, and the solver's present result on it.
- Every change of `bench/` needs the owner's approval: label the pull request `needs-owner`; CI's
  `bench approved` check fails until the owner adds the label `owner-approved`. Never add
  `owner-approved` yourself, and do not repair a pull request that only waits for it. A merged
  suite is not changed to improve results; a harder or different measure is a new suite.

### Trusted base

Not proved in this repository, and not to be presented as proved: the AutoCorrode translation, the
assumptions of the locale `Sat_heap` (AutoCorrode's reference model), and the command line `cli/`
(DIMACS input, output of the answer).
