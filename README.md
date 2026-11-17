# Sat

一个经过验证的 SAT 求解器。求解器用 Rust 写成，经 AutoCorrode 翻译到 Isabelle/HOL，
并证明它满足 `spec/` 中的规约：可满足时给出满足公式的赋值，不可满足时公式确实不可满足。主定理是
`Sat_heap.solver_correct`（`proof/top/Sat_Top.thy`）。

    cargo build --release
    target/release/sat FILE.cnf     # DIMACS 输入，SAT 竞赛格式输出

- 规约：`spec/`
- 规则：`PLAN.md`
- 开发方式：`CLAUDE.md`
- 证明的 HTML：<https://zhichenghui.github.io/Sat/>
