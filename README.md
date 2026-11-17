# Sat

一个经过验证的 SAT 求解器。求解器是 CreuSAT 中的 Friday（<https://github.com/sarsko/CreuSAT>，一个
“完全验证、极其朴素”的求解器：按变量顺序枚举全部赋值）。Rust 代码在原版基础上去掉 Creusot 注解、字段改为
`pub`，并按 SAT 竞赛的要求在可满足时返回满足的赋值。代码经 AutoCorrode 前端翻译到 Isabelle/HOL，并证明它满足
在 Friday 的 Creusot 契约基础上加强的契约（回答可满足时交出模型）。目录结构、
命名和检查流程与 QF_UF_Smt、QF_BV_Smt 两个项目一一对应。

## 目录结构

| 路径 | 内容 |
|---|---|
| `core/src/lib.rs` | 被验证的部分：求解器 `solver(f: &Formula) -> Answer`（`Answer` 是 `Sat(Assignments)` 或 `Unsat`）及其数据类型 |
| `cli/src/main.rs` | 可执行程序 `sat`（未验证）：读入 DIMACS CNF，调用 `solver`，按 SAT 竞赛格式输出 |
| `urust/` | AutoCorrode 前端从 `core/src/lib.rs` 生成的 Isabelle 翻译，session `Sat` |
| `spec/` | 顶层规约，session `Sat_Spec`。主定理的含义只取决于这个目录：`Formula_Types.thy`（生成的公式类型的形状）、`Sat_Spec.thy`（公式的语义、契约、heap locale 与主定理的陈述） |
| `proof/` | 各函数的契约与证明（`Sat_Proof.thy`，来自 Friday 的验证），session `Sat_Proof` |
| `proof/top/` | 顶层定理（`Sat_Top.thy`），session `Sat_Top` |
| `tools/` | 检查与测试脚本 |

## 构建与运行

需要 Rust 工具链：

    cargo build --release

产物为 `target/release/sat`。用法：`sat FILE.cnf`，或从标准输入读入。按 SAT 竞赛的格式输出：可满足时
输出 `s SATISFIABLE`，接着是 `v` 行，按 DIMACS 编号给出每个变量的文字（`i` 为真、`-i` 为假），以 `0` 结尾，退出码 10；
不可满足时输出 `s UNSATISFIABLE`，退出码 20；输入格式错误时在标准错误上报告，退出码 1。求解时间随变量数指数增长，几十个变量以上就不实用；性能不是这个项目的目标。

## 规约与定理

顶层规约就是 `spec/` 目录：主定理的含义只取决于其中的定义，改动求解器或证明不需要改动它，改动它就是改动规约。
规则写在 `PLAN.md`，CI 用 `tools/check-spec.sh` 检查。`spec/Formula_Types.thy` 写出从 Rust 代码生成的 `Lit`、`Clause`、
`Formula` 的每个字段及其类型，并由生成的类型证明，Rust 中这些类型一旦改变，构建就失败。`spec/Sat_Spec.thy` 中：

- `lit_sat`、`clause_sat`、`formula_sat`、`formula_invariant`：Friday 的 Creusot 逻辑函数的转写（赋值是
  `bool list`，`usize` 的数学值是 `unat`）；`sat_repr_ok f`：公式中每个列表少于 `2^63` 个元素（任何 Rust 值都满足）；
- `solver_contract f`：前置条件 `formula_invariant f ∧ sat_repr_ok f`（每个文字的变量小于变量数）；回答
  `Sat(a)` 时，`a` 给每个变量一个值（长度等于变量数）并满足 `f`；回答 `Unsat` 时，长度等于变量数的任何赋值都不
  满足 `f`；不 panic。它在 Friday 的 Creusot 契约基础上加强：可满足时交出模型，而不只是断言模型存在；
- `solver_correct Γ`：对每个满足前置条件的 `f`，存在 `N`，使翻译取任意不小于 `N` 的 fuel 时 `solver f` 满足
  `solver_contract f`。fuel 是翻译给每个循环和递归设的次数上限，对它取存在量词。

求解器只回答 `Sat` 或 `Unsat`，没有 `Unknown`，所以与 QF 两个项目不同，这里没有输入范围：契约对每个满足前置条件
的公式都成立。顶层定理是 `Sat_heap.solver_correct`（`proof/top/Sat_Top.thy`），`N` 取 `fuel_top f`（变量数加 1，
加子句数，加全部子句长度之和）。

例外：`spec/Sat_Spec.thy` 中的 locale `Sat_heap` 是生成的 `Sat_ctx`（`urust/Sat_Locale.thy`）去掉 fuel 后的副本。
求解器新增一种可变局部变量的类型时，生成的 locale 会多一个参数，`Sat_heap` 要照样更新；这是 `spec/` 中唯一随求解器
实现改变的部分。`tools/check-spec.sh` 检查两件事：去掉这个 locale 后 `spec/` 与清单 `tools/spec.sha256` 一致；这个
locale 与生成的 `Sat_ctx` 去掉 fuel 后一致。只有所有者用 `tools/check-spec.sh --update` 更新清单。

信任基础（不在本仓库中证明）：AutoCorrode 翻译的正确性（fuel 足够时翻译出的函数与 Rust 函数行为一致）；
locale `Sat_heap` 的假设（AutoCorrode 引用模型的假设）；未验证的命令行（把 DIMACS 文本转成 `Formula`，打印回答）。
程序逻辑不模拟内存和栈的耗尽，契约对它们不作断言（`solve` 的递归深度等于变量数加 1）。

## 证明的组成

| 文件 | 内容 |
|---|---|
| `proof/Sat_Proof.thy` | `Clause::eval`、`Formula::eval`、`set_next`、`solve` 的契约与证明（`solve` 按 fuel 归纳），以及带 fuel 前提的 `solver_fuel_spec` |
| `proof/top/Sat_Top.thy` | `fuel_top`；fuel 不小于 `fuel_top f` 时 `solver` 满足规约的契约（`solver_spec`）；顶层定理 `solver_correct` |

## 检查证明

    tools/check.sh [MINUTES]

检查全部证明：把 `urust/`、`spec/`、`proof/` 复制到检查机器上的任务目录
`$CHECK_WORK/sat-check-<检出目录名>/`，在那里写 `ROOTS` 和一个以任务命名的 session `SatCheck_Task`（导入顶层定理
`Sat_Top.Sat_Top`），用 `isabelle build -d`（不加 `-b`，不留 heap）在共享的 AutoCorrode heap 上构建，作为
限时 MINUTES 分钟（默认 120）、内存 16 GB 的 systemd 单元运行，结束后输出构建的 session、错误和退出码。
需要 Isabelle2026 和已构建的 AutoCorrode heap。检查机器、任务目录和 Isabelle 的位置是机器相关的配置，不在仓库里，见 `tools/check.sh` 开头的说明。CI 在每次推送和 PR 上做同样的检查，并把证明的 HTML 发布到
<https://zhichenghui.github.io/Sat/>。

## 测试

- `cargo test --release`：`core/tests/solve.rs` 直接测试 `solver`（空公式、空子句、鸽巢问题，以及与穷举比较的
  随机公式），每个返回的模型都独立检查；`cli/tests/dimacs.rs` 经命令行端到端测试 DIMACS 输入、回答、`v` 行和
  退出码，`v` 行的模型用测试自带的解析独立检查。
- `tools/fuzz.py BIN Z3 N [SEED]`：随机小 CNF 公式，与 `z3 -dimacs` 比较回答，并检查每个 `v` 行模型满足公式。

## 用 pod 派任务

仓库按 lean-zip 的做法配置了 pod（<https://github.com/kim-em/pod>，多代理管理器）：在一台机器上运行一组
Claude Code agent，每个 agent 在自己的 git worktree 和分支上工作，通过 GitHub issue 接任务、通过 PR 交付，
PR 的 CI（spec 校验、cargo test、全部证明）通过后自动 squash 合并。

- 下达任务：开一个 issue。带标签 `agent-plan` 的 issue 由 worker 直接认领去做；带标签 `directive` 的较大任务
  由 planner 拆成若干 `agent-plan` issue。只有仓库所有者和协作者写的 issue 与评论会被 agent 读到。
- 规则：`PLAN.md` 写项目规则和方向（只有所有者能改），`CLAUDE.md` 写 agent 的工作方式；agent 的每个任务在
  `progress/` 留一份工作记录。pod 拒绝为改动 `tools/spec.sha256`、`tools/check-spec.sh`、`PLAN.md`、`CLAUDE.md`、
  `.github/`、`.pod/` 的分支开 PR（`.pod/config.toml` 的 `protected_files`）；`spec/` 由 CI 的
  `tools/check-spec.sh` 把关，agent 只能按规则更新其中的 locale。
- 启动：在运行 pod 的机器上进入 pod 的工作副本，用所有者环境中的启动脚本运行 pod（`add N` 启动 N 个 agent，`list`、
  `status`、`finish all` 等见 pod 的说明）。启动脚本设置 agent 的环境（Claude Code 配置、令牌、PATH、`tools/check.sh`
  的配置），属于机器相关的配置，不在仓库里。
- agent 开发证明时，用 `tools/devcopy.sh` 生成 `dev/`（导入去掉 session 限定的扁平副本），在 Pool Server 上检查
  其中的理论；提交前 `tools/check.sh` 必须通过。

## 重新生成翻译

`core/src/lib.rs` 改动后，或前端更新后（CI 的 `translation up to date` 失败），用前端 master 分支的最新版本重新生成：

    urust-frontend.sh --out urust --name Sat core/src/lib.rs
