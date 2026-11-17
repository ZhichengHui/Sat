# Rules for this repository

- `spec/` is the specification: the meaning of the top-level theorem `solver_correct` depends on
  nothing else. It is fixed across changes of the solver and its proofs. Do not edit any file in
  `spec/` unless the user explicitly asks for that change; if a task seems to need one, stop and
  ask. CI fails when `spec/` differs from `tools/spec.sha256`.
- The contract `solver_contract` in `spec/Sat_Spec.thy` is the Creusot contract of Friday's
  `solver`: a change of the solver must keep satisfying it for every formula of the precondition.
  Make the solver fit the specification, never the specification fit the solver.
- One part of `spec/` follows the generated code: the locale `Sat_heap` in `spec/Sat_Spec.thy` is
  `Sat_ctx` of `urust/Sat_Locale.thy` without its last line (the fuel). When regenerating `urust/`
  changes that locale, update `Sat_heap` to match it exactly and tell the user.
- `urust/` is generated from `core/src/lib.rs`; never edit it by hand.
- Check all proofs with `tools/check.sh` before committing.
