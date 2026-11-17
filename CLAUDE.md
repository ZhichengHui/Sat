# Sat

A verified SAT solver: the top-level theorem `Sat_heap.solver_correct` is proved against the
specification in `spec/`.

## Build and test

These commands need cargo, z3 and the machine-specific configuration of `tools/check.sh` (see its
header); pod agents get all of it from the environment their launcher sets.

- Rust: `cargo build --release`, `cargo test --release`.
- Proofs: `tools/check.sh` checks every session; CI runs the same check on every pull
  request.
- Differential testing: `python3 tools/fuzz.py target/release/sat z3 300 SEED`.
- After changing `core/src/lib.rs`, or when CI's `translation up to date` fails: regenerate
  `urust/` with
  `"$URUST_FRONTEND_DIR"/scripts/urust-frontend.sh --out urust --name Sat core/src/lib.rs`.
  (`URUST_FRONTEND_DIR` is the front end, kept at its newest commit by the agents' launcher; if it
  is unset, stop and ask.)
  If the new translation breaks `spec/`, do not change `spec/`: report it on the issue and stop.

## Developing proofs

- Use the Isabelle Pool Server MCP (`isabelle-pool-server`) with the skills
  `isabelle-proof-development` and, for contracts, `autocorrode-contract-proofs`.
- The Pool Server cannot resolve this project's session-qualified imports. Edit the theories in
  `urust/`, `spec/`, `proof/`; run `tools/devcopy.sh`, which writes `dev/` (a flat copy with
  unqualified imports, not committed); check `dev/<Theory>.thy` with the Pool Server, giving its
  absolute path. Re-run `tools/devcopy.sh` after every edit before checking again.
- Close every file you opened with `isabelle_close` before finishing.
- Before opening a pull request, every theory you changed checks in the Pool Server without
  errors. Run `tools/check.sh` (it must end with `EXIT 0`) only when the change can break theories
  you did not open: you changed a definition or lemma that other theories use, or regenerated
  `urust/`. Otherwise CI runs the full check. In every case
  `grep -rnwE 'sorry|oops|quick_and_dirty' spec proof` must find nothing, and `tools/check-spec.sh`
  must pass.

## Layout

- `spec/` — the specification; the meaning of `solver_correct` depends on nothing else.
- `urust/` — generated; never edit by hand.
- `proof/` — the proofs.
- `core/`, `cli/` — Rust; `tools/` — checks and tests.

## Rules

The rules of this repository are in `PLAN.md` (the specification, verified code, the trusted base);
follow them. In practice:

- After regenerating `urust/`: `urust/PLACEHOLDERS.txt` must report 0, and `urust/*_Template.thy`
  must have no new stubs. If not, rewrite the code in the supported subset; in every case report
  the gap to the framework as `PLAN.md` says.
- After regenerating `urust/`, run `tools/check-spec.sh`. If it reports that the locale `Sat_heap`
  differs from the generated one, update that locale in `spec/Sat_Spec.thy` to match exactly (and
  say so in the pull request). That is the only change of `spec/` you may make.
- If a task seems to need any other change of `spec/`, do not make it: comment on the issue
  explaining why, and stop.
- After three failed attempts with the same approach, change the approach.

## Tests

Their role is in `PLAN.md`. Run `cargo test --release` (`core/tests/`) and
`python3 tools/fuzz.py target/release/<binary> z3 N SEED` when they help.

## Commits and pull requests

- Prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`, `perf:`.
- One logical change per commit; every commit builds and passes `cargo test`.
- Write the progress entry of the session in `progress/` (pod's worker flow) and commit it with
  the change.
- Do not edit `CLAUDE.md`, `PLAN.md`, `tools/spec.sha256`, `tools/check-spec.sh`, `.github/` or
  `.pod/` (pod refuses such pull requests).
