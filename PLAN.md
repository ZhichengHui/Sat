# Plan

Work on this repository is directed by its owner through GitHub issues. There is no autonomous
roadmap: planners do not invent work.

- An issue labelled `agent-plan` is a work item; a worker claims and does it.
- An issue labelled `directive` is a larger task from the owner; a planner splits it into
  `agent-plan` issues (or a worker does it directly when it is small), and closes it when its
  deliverables are merged.
- When there is no open `directive` and no unclaimed `agent-plan` issue, planners create no issues
  and signal `return-to-human`.

Constraints on every task: `CLAUDE.md` (the specification in `spec/` is fixed; every change keeps
`solver_correct` proved; `tools/check.sh` and `cargo test` pass before a pull request).
