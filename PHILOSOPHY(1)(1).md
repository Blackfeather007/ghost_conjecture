# Prompt 哲学（贯穿所有 stage）

目标：把“写对 statement”当作第一生产力。一个 *mathlib 对齐、形态最简洁* 的 statement，往往会把后续 proof 的难度降低一个数量级（少很多 typeclass/simp/目标形态问题）。

## 1) 先选对声明形态（细化：`def` / `abbrev` / `structure` / `class` / `lemma` / `theorem` / `instance`）

- `def`：用于**定义**数据/函数/谓词（包括返回 `Prop` 的谓词，如 `IsX : α → Prop := ...`）。
- `abbrev`：同 `def`，但当你希望 definitional unfolding/defeq 更轻量、对后续推理更友好时优先用它。
- `structure`：用于**打包数据与字段**（默认不走 typeclass inference）。
- `class`：仅当该结构**应该通过 typeclass inference 使用**（下游需要自动获得实例）时才用；否则优先 `structure`。
- `lemma` vs `theorem`：都用于**命题事实**（`Prop` 中断言）。若是书中主结论（原文写 Theorem）用 `theorem`，否则默认 `lemma`。
- `instance`：只用于**典范/唯一/自然**的 typeclass 实例（需要 inference 自动找到的那种）。
  - 不要用 `instance` 来陈述/证明命题；不要为了“让 simp/推理更方便”滥造实例。

> 原则：每个条目都写成“最简洁、最标准、最接近 mathlib 的形态”。

## 2) 严禁把证明塞进 term 里：全部提成 lemma

这条规则贯穿每一个 stage（statement/proof/final）：

- 不写任何内联证明片段：禁止 `(by ...)`、`⟨..., by ...⟩`、以及在更大 term 内部用 `by` 临时补证明义务。
- 如果构造 term 需要证明字段（例如 `Subtype`、结构体字段的闭包性/性质证明等）：
  1. 先写出**单独的 `lemma`**（写清 statement，binder 尽量少且规范）。
  2. 在 term 里**引用该 lemma 名称**，而不是内联 `(by ...)`。

## 3) `def` 额外约束（更严格）

- `def` 定义体内禁止任何 `by ...`（不写 tactic proof，也不写 term-mode 的 `by` 块）。
- `def` 尽可能短：优先用纯 term 形式构造（`:=` + `fun` / `⟨...⟩` / `{ ... }` 等）。
- `def` 若必须留占位：写 `:= sorry`（不要写 `by sorry`）。

## 4) stage 1（statement 阶段）的占位风格

- 命题类（`lemma`/`theorem`）用 `:= sorry` 作为占位证明（避免 `by ...`）。
- 不使用 `axiom` 逃避证明义务（除非上层全局规则另有明确允许/要求）。

## 5) “好 statement”检查清单（写之前先过一遍）

- 是否复用 mathlib 现有结构/定义/谓词，而不是自造？
- binder 是否最少且 canonical（避免不必要的参数、避免乱加 typeclass）？
- 是否把“对象的定义”和“对象满足的性质/义务”拆开（定义用 `def`，性质用 `lemma`）？
- 是否避免在 term 内埋证明（全部抽 lemma）？
- 是否避免引入非必要的 `instance`（只留 truly canonical 的实例）？
- 是否每个新声明都有自然语言注释（docstring），方便后续维护与复用？

## 6) 注释（docstring）是硬性要求

贯穿所有 stage：

- 每次新增 `def` / `abbrev` / `structure` / `class` / `lemma` / `theorem` / `instance`，都必须在其正上方写一段简短自然语言 docstring：`/-- ... -/`。
- 不要把一段长注释“覆盖很多声明”来糊弄；要求是**每个声明各自一段**（可以很短，但要说明“它在干什么/为什么存在/与书中条目或当前目标的关系”）。
- docstring 应避免重复大段原文，强调可读性与可维护性：说明对象/命题含义、关键假设、用途即可。

## 7) 证明脚本的稳定性（避免 deterministic timeout）

- 写证明时避免“很多、且嵌套很深的 `have` 链”（尤其是 `have` 里面再 `have`），这类形态容易触发 deterministic timeout。
- 优先把中间推理拆成少量 helper lemma（配 docstring），让主证明结构保持扁平：`intro` / `refine` / `calc` / `rw` / `simp` 等。
- 如果某个证明需要很多中间结论才能推进，这通常意味着 statement/helper 形态不够好：回到前面的哲学，先把对象/谓词定义干净、把义务提成 lemma、把 binder 简化到最小。

如果这份哲学和某个分支/项目的 AGENTS 全局规则冲突，以该分支的 AGENTS 为准；否则默认按本文件执行。
