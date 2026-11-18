# Sat

A verified SAT solver: the top-level theorem `Sat_heap.solver_correct` is proved against the
specification in `spec/`.

## Build and test

These commands need cargo, z3 and the commands of the agents' environment (`isabelle-check`,
`isabelle-devcopy`); pod agents get all of it from their launcher.

- Rust: `cargo build --release`, `cargo test --release`.
- Proofs: `isabelle-check` checks every session; CI runs the same check on every pull request.
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
  `urust/`, `spec/`, `proof/`; run `isabelle-devcopy`, which writes `dev/` (a flat copy with
  unqualified imports, not committed); check `dev/<Theory>.thy` with the Pool Server, giving its
  absolute path. Re-run `isabelle-devcopy` after every edit before checking again.
- Close every file you opened with `isabelle_close` before finishing.
- Before opening a pull request, every theory you changed checks in the Pool Server without
  errors. Run `isabelle-check` (it must end with `EXIT 0`) only when the change can break theories
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
  say so in the pull request). If a generated function in `spec/` now takes other prisms, update
  its prism list (between `reference_raw_fun` and `fuel`) to the prisms it takes, in order. These
  are the only changes of `spec/` you may make.
- If a task seems to need any other change of `spec/`, do not make it: comment on the issue
  explaining why, label the issue
  `needs-owner`, and stop: end the session without `coordination skip` (`PLAN.md`, Direction).
- After three failed attempts with the same approach, change the approach.

## Tests

Their role is in `PLAN.md`. Run `cargo test --release` (`core/tests/`) and
`python3 tools/fuzz.py target/release/<binary> z3 N SEED` when they help.

## Benchmarks

Their rules are in `PLAN.md`. `bench/active` lists the active suites; run one with
`bench/run.sh SUITE` on the release build. The pull request of a new suite also adds it to
`bench/active`. A pull request that changes `bench/` gets the label `needs-owner` and waits for
the owner's label `owner-approved`.

## Commits and pull requests

- Prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`, `perf:`.
- One logical change per commit; every commit builds and passes `cargo test`.
- Write the progress entry of the session in `progress/` (pod's worker flow) and commit it with
  the change.
- Do not edit `CLAUDE.md`, `PLAN.md`, `tools/spec.sha256`, `tools/check-spec.sh`, `.github/` or
  `.pod/` (pod refuses such pull requests).
