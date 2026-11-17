# Sat

A verified SAT solver: Friday of CreuSAT in Rust (`core/src/lib.rs`), translated to Isabelle by the
AutoCorrode front end (`urust/`), with the top-level theorem `Sat_heap.solver_correct` proved in
`proof/top/Sat_Top.thy` against the specification in `spec/`. The DIMACS command line `cli/` is not
verified.

## Build and test

These commands work on the PGR compute server, where pod agents run (`tools/pod-remote.sh` sets up
PATH and HOME), and on the user's machine.

- Rust: `cargo build --release`, `cargo test --release`.
- Proofs: `tools/check.sh` checks every session (on the server it runs there directly, in about a
  minute plus the time of the proofs; its task directory is named after the checkout, so worktrees do
  not collide). CI runs the same check on every pull request.
- Differential testing: `python3 tools/fuzz.py target/release/sat z3 300 SEED` (random small CNF
  formulas, answers compared with z3).
- After changing `core/src/lib.rs`, or when CI's `translation up to date` fails: regenerate
  `urust/` with the newest front end (never pinned): `git -C $RT/AutoCorrodeRustFrontEnd pull -q`,
  `cargo build --release` there, then
  `$RT/AutoCorrodeRustFrontEnd/scripts/urust-frontend.sh --out urust --name Sat core/src/lib.rs`.
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
- `proof/` — the contract proofs (`Sat_Proof.thy`) and the top level (`top/Sat_Top.thy`).
- `core/`, `cli/` — Rust; `tools/` — checks, fuzzing, the pod launcher.

## Rules

The rules of this repository are in `PLAN.md` (the specification, verified code, the trusted base);
follow them. In practice:

- After regenerating `urust/`, run `tools/check-spec.sh`. If it reports that the locale `Sat_heap`
  differs from the generated one, update that locale in `spec/Sat_Spec.thy` to match exactly (and
  say so in the pull request). That is the only change of `spec/` you may make.
- If a task seems to need any other change of `spec/`, do not make it: comment on the issue
  explaining why, and stop.
- After three failed attempts with the same approach, change the approach.

## Tests

- A change of behaviour of the Rust code gets a test in `core/tests/` or `cli/tests/`, including
  edge cases (empty formula, empty clause).

## Commits and pull requests

- Prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`, `perf:`.
- One logical change per commit; every commit builds and passes `cargo test`.
- Write the progress entry of the session in `progress/` (pod's worker flow) and commit it with
  the change.
- Do not edit `CLAUDE.md`, `PLAN.md`, `tools/spec.sha256`, `tools/check-spec.sh`, `.github/` or
  `.pod/` (pod refuses such pull requests).
