# Single-scale concentration of non-constant gates under random restriction / 随机限制下非常数门数的单尺度集中

Author / 作者: @macchacat (with Claude)

[English](#english) · [中文](#中文)

---

## English

**Context.** Chen–Tal–Wang (ECCC TR26-039) discard "bad" columns, i.e. columns of a random restriction on which more than T = n^{2−ε/2} bottom gates are non-constant. Their Markov bound gives bad-column mass n^{−ε/3}. Upgrading their n^{2.5−ε} lower bound to correlation 1/2 + n^{−c} would need mass n^{−D}. The lemmas below give such a bound for gate families that are *regular* (R) and *free of low-dimensional clustering* (S).

**Status.**
- An adversarial referee checked Lemmas A–C and found them correct. The constants are loose: C ≈ 2 suffices, with no √p factor, and the error term is (p+1)·m^p·n^{−D}.
- The reduction of *arbitrary* gate families to (R)+(S) is **not** established. Two attempted reductions were wrong; see Scope.
- This document is **not** a circuit lower bound.

### Setting
- Gates: w_1, …, w_m ∈ ℤ^n with thresholds t_1, …, t_m.
- Column: a fixed set I ⊆ [n] of k live coordinates, O = [n] ∖ I, and z ∈ {0,1}^O uniform.
- Band and event: gate i is non-constant on the column (I, z) iff ⟨w_i^O, z⟩ ∈ t_i − (lo_i, hi_i], where lo_i = Σ_{ℓ∈I} min(w_{iℓ}, 0) and hi_i = Σ_{ℓ∈I} max(w_{iℓ}, 0). Call this event E_i. The interval has length band_i = ‖w_i^I‖₁.
- Count: J = Σ_i 1[E_i]. Put σ_i := ‖w_i^O‖₂/2 (the standard deviation of ⟨w_i^O, z⟩) and q_i := band_i/σ_i. Let ŵ_i := w_i^O/‖w_i^O‖₂.

### Lemma A (multidimensional Bernoulli small ball)
**Assumptions.**
- Let x_1, …, x_N ∈ ℝ^p and V = Σ_ℓ z_ℓ x_ℓ, with z_ℓ ∈ {0,1} independent and uniform.
- Let G = Σ_ℓ x_ℓ x_ℓᵀ, and M ≥ max_ℓ ‖x_ℓ‖.

**Claim.** For every c ∈ ℝ^p and every R > 0, with b = R²/(2p),

  Pr[‖V − c‖ ≤ R] ≤ e^{p/2} · ( (b^{p/2} / det(bI + G/12)^{1/2}) + 2^{p/2} e^{−b/M²} ).

*Proof.* This is the argument of [`lean/ProblemQ/Smoothing.lean`](../lean/ProblemQ/Smoothing.lean) (`small_ball`), with the i.i.d. selection model replaced by independent Bernoulli coefficients.
1. **Smoothing.** 1[‖u‖ ≤ R] ≤ e^{p/2} e^{−‖u‖²/(4b)}.
2. **Gaussian identity.** e^{−‖u‖²/(4b)} = (b/π)^{p/2} ∫ e^{−b‖v‖²} e^{i⟨u,v⟩} dv.
3. **Exchange.** Swapping E and ∫ gives
   E e^{−‖V−c‖²/(4b)} ≤ (b/π)^{p/2} ∫ e^{−b‖v‖²} Π_ℓ |cos(⟨v, x_ℓ⟩/2)| dv.
4. **Small frequencies.** Use |cos(θ/2)| ≤ exp(−θ²/12) for |θ| ≤ 2. The constant 1/12 works because cos(y) ≤ 1 − (43/96)y² ≤ e^{−(43/96)y²} for |y| ≤ 1, with y = θ/2, and 43/384 ≥ 1/12. On ‖v‖ ≤ 2/M every |⟨v, x_ℓ⟩| ≤ 2, so the product is ≤ e^{−vᵀGv/12}.
   The resulting Gaussian integral is ≤ π^{p/2} det(bI + G/12)^{−1/2}.
5. **Large frequencies.** On ‖v‖ > 2/M, bound the product by 1. Then (b/π)^{p/2} ∫_{‖v‖>2/M} e^{−b‖v‖²} dv ≤ 2^{p/2} e^{−2b/M²}, by the Gaussian tail estimate used in the Lean file (pass to e^{−(b/2)‖v‖²}).
6. **Combine.** Steps 1–5 give the claim. ∎

### Lemma B (joint band probability of a well-conditioned tuple)
**Assumptions.** Let P = {j_1, …, j_p} be a set of gates such that:
- (R) Regularity: band_j ≥ ρ·max_{ℓ∈O} |w_{jℓ}| for every j ∈ P, where ρ := 4p·√(D ln n);
- (W) δ-well-conditioned: for every j ∈ P, dist(ŵ_j, span{ŵ_{j'} : j' ∈ P, j' ≠ j}) ≥ δ.

**Claim.**  Pr[∧_{j∈P} E_j] ≤ (C√p/δ)^p · Π_{j∈P} q_j + n^{−D},  with C an absolute constant.

*Proof.*
1. **Rescale.** Let Δ = diag(band_j). Apply Lemma A to x_ℓ := Δ^{−1}(w_{jℓ})_{j∈P} with R = √p (the box ∏ intervals ⊆ a ball of radius √p after rescaling).
2. **Diameter.** ‖x_ℓ‖ ≤ √p·max_j |w_{jℓ}|/band_j ≤ √p/ρ =: M. So b/M² = (1/2)ρ²/p ≥ 8p·D ln n, and the tail term is ≤ n^{−D} for n large.
3. **Determinant.** G = Δ^{−1} W Wᵀ Δ^{−1}, where W is the p × |O| matrix of the rows w_j^O. Then det G = det(ŴŴᵀ) · Π_j (‖w_j^O‖₂/band_j)².
4. **Gram–Schmidt.** det(ŴŴᵀ) = Π_j dist(ŵ_j, span(previous))² ≥ δ^{2(p−1)} by (W).
5. **Conclusion.** b^{p/2} det(G/12)^{−1/2} = (1/2)^{p/2}·12^{p/2}·δ^{−(p−1)}·Π_j band_j/‖w_j^O‖₂. With ‖w_j^O‖₂ = 2σ_j this gives (C√p/δ)^p Π q_j after absorbing constants (C ≤ 12, say). ∎

### Lemma C (p-th factorial moment and tail)
**Assumptions.**
- (R) holds for every gate.
- (S) No subspace H ⊆ ℝ^O of dimension ≤ p − 1 has more than L of the ŵ_i within distance δ of H.

Write μ := Σ_i q_i and A_t := Σ_{|P|=t} Pr[∧_{j∈P} E_j], so that A_t = E C(J, t).

**Claim.**
  A_p ≤ Σ_{a=0}^{p} (C√p/δ)^a (μ^a/a!) · (pL)^{p−a} + p·m^p n^{−D},
and therefore
  Pr[J ≥ T] ≤ A_p / C(T, p) ≤ ( e·p·((C√p/δ)μ + pL) / T )^p + m^p n^{−D}·(p/T)^p·e^p.

*Proof.* Induction on t.
1. **Well-conditioned sets.** If a t-set P satisfies (W) at scale δ, Lemma B bounds its contribution by (C√t/δ)^t Π q_j + n^{−D}. Summing over such P gives ≤ (C√p/δ)^t μ^t/t! + m^t n^{−D}.
2. **Ill-conditioned sets.** Otherwise some j ∈ P has ŵ_j within δ of span(P ∖ j), a subspace of dimension ≤ t − 1 ≤ p − 1. Bound Pr[P] ≤ Pr[P ∖ j]. For each (t−1)-set Q, by (S) at most L indices j are within δ of span(Q). So these P contribute ≤ t·L·A_{t−1}, the factor t accounting for the choice of the removed index.
3. **Recursion.** Hence A_t ≤ (C√p/δ)^t μ^t/t! + tL·A_{t−1} + m^t n^{−D}. Unrolling gives the stated bound.
4. **Tail.** Markov's inequality applied to C(J, p) gives the tail bound. ∎

### Parameters for CTW at size m = n^{2.5−ε}
Take k = n^{ε/10} and T = n^{2−ε/2} (CTW's goodness threshold).
- **First moment.** For regular gates, q_i ≈ band_i/σ_i ≈ k/√n up to the regularity profile, so μ ≈ m·k/√n = n^{2−0.9ε}.
- **Choice of p.** Choose δ := n^{−0.1ε}, L := T·n^{−0.3ε}, and p := ⌈D/(0.1ε)⌉.
- **Ratio.** Then (C√p/δ)μ + pL ≤ n^{2−0.8ε}·O(√p) + p·n^{2−0.8ε}, so e·p(…)/T ≤ n^{−0.3ε}·O(p²).
- **Conclusion.** The tail is ≤ n^{−0.3εp}·poly ≤ n^{−D+O(1)}, and the error term m^p n^{−D} is absorbed by running Lemma B with D' = D + 3p.

**Corollary.** Every family satisfying (R) and (S) at these parameters has bad-column mass (J > T) ≤ n^{−D}. This settles the single-scale case only; see Scope below.


### Scope

The corollary covers only families satisfying (R) and (S).

Two natural reductions from general families fail:
1. **"τ-regular ⇒ (R)" is false.** Counterexample: n^{1/4} coordinates of weight n^{1/4}, the rest of weight 1.
2. **Dropping small residuals of near-parallel clusters is false.** It fails at lattice atoms. Counterexample: w_i = A·𝟙 + u_i, which errs with probability about 1/√n.

A plausible route to the general case is an arithmetic structure theorem, via the continuous high-dimensional inverse Littlewood–Offord theorem of Nguyen–Vu ([arXiv 1004.3967](https://arxiv.org/abs/1004.3967), Thm 2.9). It has not been carried out.

---

## 中文

**背景。** Chen–Tal–Wang（ECCC TR26-039）会丢弃「坏列」：随机限制下，非常数底层门超过 T = n^{2−ε/2} 个的列。他们的 Markov 估计给出的坏列质量是 n^{−ε/3}。若要把 n^{2.5−ε} 下界升级为相关性 1/2 + n^{−c}，需要把坏列质量压到 n^{−D}。下面的引理对满足**正则性 (R)** 与**无低维聚集 (S)** 的门族给出了这样的界。

**状态。**
- 引理 A–C 经过对抗性审稿，确认正确。常数可以更紧：C ≈ 2 即可，不需要 √p 因子；误差项为 (p+1)·m^p·n^{−D}。
- 把**任意**门族化归到 (R)+(S) 的部分**尚未**完成，两处化归尝试是错的，见「适用范围」。
- 本文**不是**电路下界。

### 设定
- 门：w_1, …, w_m ∈ ℤ^n，阈值为 t_1, …, t_m。
- 列：k 个活跃坐标组成的固定集合 I ⊆ [n]，O = [n] ∖ I，z ∈ {0,1}^O 均匀随机。
- 带与事件：门 i 在列 (I, z) 上非常数，当且仅当 ⟨w_i^O, z⟩ ∈ t_i − (lo_i, hi_i]，其中 lo_i = Σ_{ℓ∈I} min(w_{iℓ}, 0)，hi_i = Σ_{ℓ∈I} max(w_{iℓ}, 0)。记此事件为 E_i，区间长度为 band_i = ‖w_i^I‖₁。
- 计数：J = Σ_i 1[E_i]。令 σ_i := ‖w_i^O‖₂/2（即 ⟨w_i^O, z⟩ 的标准差），q_i := band_i/σ_i，ŵ_i := w_i^O/‖w_i^O‖₂。

### 引理 A（多维 Bernoulli 小球估计）
设 x_1, …, x_N ∈ ℝ^p，V = Σ_ℓ z_ℓ x_ℓ，其中 z_ℓ ∈ {0,1} 独立均匀。令 G = Σ_ℓ x_ℓ x_ℓᵀ，M ≥ max_ℓ ‖x_ℓ‖。则对任意 c ∈ ℝ^p 与 R > 0，取 b = R²/(2p)，有

  Pr[‖V − c‖ ≤ R] ≤ e^{p/2} · ( b^{p/2} / det(bI + G/12)^{1/2} + 2^{p/2} e^{−b/M²} )。

证明沿用 [`lean/ProblemQ/Smoothing.lean`](../lean/ProblemQ/Smoothing.lean) 中的高斯平滑论证：
1. 用高斯核光滑化指示函数，再写成 Fourier 积分并交换期望与积分。
2. 低频部分用 |cos(θ/2)| ≤ e^{−θ²/12}（|θ| ≤ 2）。
3. 高频部分用高斯尾估计。

### 引理 B（良态元组的联合概率）
设 P = {j_1, …, j_p}，满足：
- (R) 对每个 j ∈ P，band_j ≥ ρ·max_{ℓ∈O}|w_{jℓ}|，其中 ρ = 4p√(D ln n)；
- (W) 对每个 j ∈ P，ŵ_j 到其余 ŵ 张成空间的距离 ≥ δ。

则 Pr[∧_{j∈P} E_j] ≤ (C√p/δ)^p · Π_j q_j + n^{−D}。

证明：
1. 按 band_j 缩放后套用引理 A，取 R = √p。
2. (R) 保证尾项 ≤ n^{−D}。
3. Gram–Schmidt 给出 det(ŴŴᵀ) ≥ δ^{2(p−1)}，从而主项化为单门概率的乘积。

### 引理 C（p 阶阶乘矩与尾部）
设 (R) 对所有门成立，且 (S)：任何维数 ≤ p−1 的子空间 H，与之距离 ≤ δ 的 ŵ_i 至多 L 个。令 μ = Σ_i q_i，A_t = E·C(J, t)。则有递推

  A_t ≤ (C√p/δ)^t μ^t/t! + t·L·A_{t−1} + m^t n^{−D}，

从而 Pr[J ≥ T] ≤ (e·p·((C√p/δ)μ + pL)/T)^p + （可忽略项）。

递推的两种情形：
- 良态集合用引理 B。
- 病态集合中，存在某个 j 落在其余元素张成空间的 δ 邻域内，此时用 Pr[P] ≤ Pr[P∖j]，再由 (S) 计数。

### CTW 参数
m = n^{2.5−ε}，k = n^{ε/10}，T = n^{2−ε/2}，μ ≈ n^{2−0.9ε}。取 δ = n^{−0.1ε}，L = T·n^{−0.3ε}，p = ⌈D/(0.1ε)⌉，即得尾部 ≤ n^{−D+O(1)}。

**推论。** 满足 (R) 与 (S) 的门族，坏列质量 ≤ n^{−D}。这只解决了单尺度情形，见「适用范围」。

### 适用范围
推论只覆盖满足 (R)+(S) 的门族。从一般门族出发的两个自然化归都是错的：
1. **「τ-正则 ⇒ (R)」不成立。** 反例：n^{1/4} 个坐标的权重为 n^{1/4}，其余权重为 1。
2. **「丢掉近平行簇的小残差」不成立。** 它在格点原子处失效。反例：w_i = A·𝟙 + u_i，出错概率约为 1/√n。

一般情形的可能出路，是借助 Nguyen–Vu 的连续高维逆 Littlewood–Offord 定理（[arXiv 1004.3967](https://arxiv.org/abs/1004.3967) Thm 2.9）建立算术结构定理，目前尚未完成。
