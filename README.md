# Depth-2 threshold circuits beyond n^{2.5}: method barriers and verified lemmas / 深度 2 阈值电路超越 n^{2.5}：方法屏障与已验证引理

Author / 作者: @macchacat (with Claude)

[English](#english) · [中文](#中文)

---

## English

This repository collects the verified results from a research effort around the n^{2.5−ε} lower bound for THR∘THR (depth-2 threshold circuits) of Chen–Tal–Wang ([ECCC TR26-039](https://eccc.weizmann.ac.il/report/2026/039/), STOC 2026).

**What it is not.** It does **not** contain a new circuit lower bound. The results are of three kinds:
1. Barriers that show where a *method* stops.
2. Lemmas toward stronger bounds.
3. Exact computations for open combinatorial questions.

Every item is either kernel-checked in Lean, refereed on paper, or reproducible by the included code. Each item is labelled with its status.

### Contents

| Path | What | Status |
| --- | --- | --- |
| [`lean/`](lean/) | Lean 4 + Mathlib formalization; see [`lean/README.md`](lean/README.md) for every statement | No `sorry`, no custom axioms (only `propext`, `Classical.choice`, `Quot.sound`); `leanchecker --fresh` full kernel replays pass |
| [`docs/concentration.md`](docs/concentration.md) | Single-scale concentration of non-constant gates under random restriction (Lemmas A–C) | Paper proof, checked by an adversarial referee; covers only regular, non-clustered gate families |
| [`docs/equality-covers.md`](docs/equality-covers.md) | Equality-matrix covers of Disjointness; exact hyperplane covers; the Diamond–Yehudayoff conjecture | Lower bound proved (minor sharpening of known results); upper bound not refereed; computations reproducible |
| [`code/`](code/) | SAT / annealing / MILP / exact-enumeration code; a verified cover of DISJ_7 by 8 equality matrices | Run as described below |

### Main verified results (Lean)

- **Barriers for the Chen–Tal–Wang template beyond n^{2.5}.**
  - **Theorem 3′** (`ProblemQ.barrier`): oblivious window certificates cannot certify columns of random THR circuits with ≥ C·n^{2.5} gates.
  - **R3** and its uniform version: 4-wise independent layering families cannot balance, even when chosen adaptively and with y-dependent centers.
  - **NL-U** (`nl_u`, `nl_u_ctw`): the same holds for arbitrary low-degree non-linear list approximations, at CTW's growth rates.
  - **NL-SYM** with periodic Smolensky (`nl_sym`): fixed-symmetric-function variant.
- **Lemmas for the CAPP (approximate counting) route.**
  - Erdős–Littlewood–Offord via Sperner (`erdos_lo`).
  - Tail dependence of halfspaces (`pair_corr_ge`).
  - Restricted-to-full row transfer (`transfer`).
  - Bernstein concentration under restriction (`transfer_pm1`).
  - Bottom fan-in below n cannot compute parity (`not_parity`).
  - Exact-threshold reductions (`top_ethr_of_ethr`, `and_eq_zero_iff`, `parity_ethr`).

These are barriers against a **method**, not lower bounds against circuits. See the Scope section of [`lean/README.md`](lean/README.md).

### Candidate new lower bounds that were checked and rejected

| Candidate | Verdict |
| --- | --- |
| ETHR∘ETHR / MTHR∘THR at n^{2.5−ε} | Correct, but a routine corollary of CTW |
| Depth-3 G_k∘SYM∘THR, k ≤ n^{ε/100} | Correct, footnote-level adaptation of CTW Thm 5.4 |
| Almost-everywhere average-case n^{2.5−ε} | Remark-level; conditional on an unrefereed transfer theorem |
| AETM ≠ ETHR∘ETHR (Hansen–Podolskii's open question) | Blocked: natural witnesses contain INTERSECTION, so putting them in ETHR∘ETHR would refute the Orthogonal Vectors Conjecture (Williams 2024) |
| Heavy exact-threshold tops for the Chattopadhyay–Mande sign-rank method | Fails: the anchored margin the method needs stays bounded |
| Exact hyperplane covers of the inner-product-zero set, ec ≥ 2^{n/4−1} | Folklore (Jukna 2006 + Williams 2024) |

### Reproducing

```bash
cd lean && lake build ProblemQ
```

```bash
python3 code/verify_cover.py code/covers/disj7_r8.txt
```

```bash
python3 code/dy_affine.py 3
```

```bash
python3 code/eqmax.py 4
```

`code/eqcover.py` needs [PySAT](https://pysathq.github.io/) and `code/eqmax.py` needs SciPy. `code/sa_cover.c` and `code/dy_affine.c` are plain C:

```bash
gcc -O2 -o sa_cover code/sa_cover.c -lm
```

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (pinned in `lean/lake-manifest.json`).

### References

- Chen, Tal, Wang, ECCC TR26-039 (STOC 2026).
- Hansen, Podolskii, *Exact threshold circuits*, CCC 2010.
- Chattopadhyay, Mande, ECCC TR17-083 / SICOMP 2022.
- Williams, *The Orthogonal Vectors Conjecture and Non-Uniform Circuit Lower Bounds*, ECCC TR24-142 (FOCS 2024).
- Alman, Li, *Kronecker Powers, Orthogonal Vectors, and the Asymptotic Spectrum*, arXiv 2509.14489 (FOCS 2025).
- Diamond, Yehudayoff, *Explicit exponential lower bounds for exact hyperplane covers*, ECCC TR21-148 (Discrete Math 2022).
- Jukna, *On graph complexity*, CPC 2006.
- Nguyen, Vu, *Optimal inverse Littlewood–Offord theorems*, arXiv 1004.3967.

### License

- **Code** (`lean/`, `code/`): [MIT](LICENSE).
- **Documentation** (`README.md`, `docs/`, `lean/README.md`): [CC BY 4.0](LICENSE-CC-BY-4.0.txt). Please credit @macchacat.

---

## 中文

本仓库整理了围绕 Chen–Tal–Wang 的 THR∘THR（深度 2 阈值电路）n^{2.5−ε} 下界（[ECCC TR26-039](https://eccc.weizmann.ac.il/report/2026/039/)，STOC 2026）所做研究中**已经验证过**的结果。

**本仓库不是什么。** 这里**没有**新的电路下界。内容分三类：
1. 说明某种**方法**在哪里止步的屏障定理。
2. 通向更强下界的引理。
3. 针对开放组合问题的精确计算。

每一项要么在 Lean 中经过内核检查，要么有经过审稿的纸面证明，要么能用附带代码复现，并都标明了状态。

### 目录

| 路径 | 内容 | 状态 |
| --- | --- | --- |
| [`lean/`](lean/) | Lean 4 + Mathlib 形式化，全部陈述见 [`lean/README.md`](lean/README.md) | 无 `sorry`、无自定义公理（只用 `propext`、`Classical.choice`、`Quot.sound`），`leanchecker --fresh` 全量内核重放通过 |
| [`docs/concentration.md`](docs/concentration.md) | 随机限制下非常数门数的单尺度集中（引理 A–C） | 纸面证明，经对抗性审稿确认；只覆盖正则且无低维聚集的门族 |
| [`docs/equality-covers.md`](docs/equality-covers.md) | Disjointness 的等式矩阵覆盖、超平面恰好覆盖、Diamond–Yehudayoff 猜想 | 下界已证（对已知结果的小幅改进）；上界未经审稿；计算可复现 |
| [`code/`](code/) | SAT、模拟退火、MILP、精确枚举代码；DISJ_7 的 8 等式矩阵覆盖（已验证） | 运行方式见下文 |

### 主要的已验证结果（Lean）

- **Chen–Tal–Wang 模板在 n^{2.5} 之外的屏障。**
  - **定理 3′**（`ProblemQ.barrier`）：对 ≥ C·n^{2.5} 个门的随机 THR 电路，事先固定的窗口证书无法认证足够多的列。
  - **R3** 及其一致版本：4 重独立的分层族无法做到平衡，即使在看到电路后自适应选择、并允许依赖 y 的中心也不行。
  - **NL-U**（`nl_u`、`nl_u_ctw`）：任意低次非线性列表逼近也一样，并且在 CTW 的参数增长率下成立。
  - **NL-SYM**（周期 Smolensky，`nl_sym`）：固定对称函数的版本。
- **CAPP（近似计数）路线的引理。**
  - 用 Sperner 定理证明的 Erdős–Littlewood–Offord（`erdos_lo`）。
  - 半空间的尾部相关性（`pair_corr_ge`）。
  - 从限制行到全行的迁移（`transfer`）。
  - 随机限制下的 Bernstein 集中（`transfer_pm1`）。
  - 底层扇入小于 n 时无法计算奇偶（`not_parity`）。
  - 精确阈值电路的初等规约（`top_ethr_of_ethr`、`and_eq_zero_iff`、`parity_ethr`）。

这些是针对**方法**的屏障，不是针对电路的下界，详见 [`lean/README.md`](lean/README.md) 的 Scope 一节。

### 检查过并被否定的新下界候选

| 候选 | 结论 |
| --- | --- |
| ETHR∘ETHR / MTHR∘THR 的 n^{2.5−ε} | 正确，但只是 CTW 的常规推论 |
| 深度 3 的 G_k∘SYM∘THR，k ≤ n^{ε/100} | 正确，是 CTW Thm 5.4 的脚注级改写 |
| 几乎处处的平均情形 n^{2.5−ε} | remark 级，且依赖一个未经审稿的迁移定理 |
| AETM ≠ ETHR∘ETHR（Hansen–Podolskii 的开放问题） | 被屏障挡住：自然的见证函数都含 INTERSECTION，把它们放进 ETHR∘ETHR 会推翻正交向量猜想（Williams 2024） |
| 用「重」的精确阈值顶层配合 Chattopadhyay–Mande 的符号秩方法 | 失败：该方法需要的锚定间隔一直有界 |
| 内积零集的超平面恰好覆盖 ec ≥ 2^{n/4−1} | 民间已知（Jukna 2006 + Williams 2024） |

### 复现

```bash
cd lean && lake build ProblemQ
```

```bash
python3 code/verify_cover.py code/covers/disj7_r8.txt
```

```bash
python3 code/dy_affine.py 3
```

```bash
python3 code/eqmax.py 4
```

`code/eqcover.py` 需要 [PySAT](https://pysathq.github.io/)，`code/eqmax.py` 需要 SciPy；`code/sa_cover.c` 与 `code/dy_affine.c` 是普通 C 程序：

```bash
gcc -O2 -o sa_cover code/sa_cover.c -lm
```

工具链：Lean `v4.34.1`、Mathlib `v4.34.1`（版本固定在 `lean/lake-manifest.json`）。

参考文献见上方英文部分。

### 许可证

- **代码**（`lean/`、`code/`）：[MIT](LICENSE)。
- **文档**（`README.md`、`docs/`、`lean/README.md`）：[CC BY 4.0](LICENSE-CC-BY-4.0.txt)，转载或改编请署名 @macchacat。
