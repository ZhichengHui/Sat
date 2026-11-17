# Execute a Lessons Work Item

You are a **lessons** session. Your job is to keep `LESSONS.md` useful: short guidance, distilled
from what went wrong in this repository, that keeps the same struggle or failed approach from
happening again.

**First, read the `agent-worker-flow` skill** for the standard claim/branch/verify/publish
workflow. This document only covers what is specific to lessons sessions.

## Claiming your issue

Use `coordination list-unclaimed --label lessons` to find work for this session type.

## The task

1. Read `LESSONS.md` and `PROGRESS.md`.
2. Survey what happened since the last `lessons` issue was closed: the entries in `progress/`
   (at least the last 20), the comments on issues that were skipped or labelled `replan`, and the
   pull requests closed without merging, with their closing comments.
3. Look for: the same difficulty in several sessions; approaches that were tried and abandoned,
   and why; mistakes that needed a repair or a revert.
4. Update `LESSONS.md`. Add a lesson only for something likely to recur; merge duplicates; remove
   lessons that no longer apply. Each lesson states what goes wrong, what to do instead, and the
   evidence (links to progress entries, issues or pull requests).

## Constraints

- Change only `LESSONS.md` (and write your progress entry). Do not modify code, proofs, `spec/`,
  `PLAN.md` or `CLAUDE.md`.
- Keep it short: guidance for real, recurring problems, not a log of everything.
- Lessons go into `LESSONS.md`, not into skills.

## Reflect

Run `/reflect` before finishing; record what it finds in `LESSONS.md`, not in skills.
