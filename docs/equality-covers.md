# Equality-matrix covers of Disjointness and exact hyperplane covers / Disjointness 的等式矩阵覆盖与超平面恰好覆盖

Author / 作者: @macchacat (with Claude)

[English](#english) · [中文](#中文)

---

## English

### Summary

| Statement | Status | Where |
| --- | --- | --- |
| A single equality matrix inside DISJ_d has ≤ (3√3/2)^d ones, so cov(d) ≥ (2/√3)^d | Proved here (entropy). Implied up to a poly(d) factor by Alman–Li's covering degree, so this is a minor sharpening | §1 |
| cov(d) ≤ d^{O(1)}·(2/√3)^d | Explicit finite bound proved here, not refereed. The exponent is computed numerically; the closed-form max–min is not written out | §2 |
| cov(7) ≤ 8, i.e. 8^{1/7} ≈ 1.3459 < 6^{1/6} | Computer-found cover, independently verified | §3, `code/covers/disj7_r8.txt` |
| cov(7) ≤ 7 | Not found in 36 annealing runs (best leaves 5 pairs uncovered). Open | §3 |
| Diamond–Yehudayoff conjecture (a hyperplane contained in D_n has ≤ 2^{n/2} cube points) | Verified exactly for d = n/2 ≤ 3 over all real weights. Open in general | §4 |
| Exact hyperplane covers of the inner-product-zero set: ec ≥ 2^{n/4−1} | Folklore: Jukna 2006 Cor. 3.10 together with Williams 2024's "ETHR gate = equality matrix" | §5 |

**Definitions.**
- **DISJ_d** is the 2^d × 2^d matrix with DISJ_d[x,y] = 1 iff x ∩ y = ∅, for x, y ⊆ [d]. It has 3^d ones.
- An **equality matrix** (Williams, [ECCC TR24-142](https://eccc.weizmann.ac.il/report/2024/142/)) is M[x,y] = [u(x) = v(y)].
- **cov(d)** is the least t such that DISJ_d is the entrywise OR of t equality matrices, each of whose ones lie inside DISJ_d. Such an OR is a weak-equality-rank decomposition, so weak-eq-rank(DISJ_d) ≤ cov(d).

### 1. Lower bound

**Lemma.** Every equality matrix M inside DISJ_d has at most (3√3/2)^d ones.

*Proof.*
1. **Setup.** Let (X, Y) be uniform over the N ones of M, with label L = u(X) = v(Y). For each label ℓ let S_ℓ be the union of the rows labelled ℓ. Every column labelled ℓ is disjoint from S_ℓ.
2. **Two identities.** Given L, the pair (X, Y) is uniform on a rectangle, and L is a function of X and also of Y. Hence log₂N = H(X) + H(Y|L) = H(Y) + H(X|L).
3. **Entropy bounds.** Put α = E|X|/d, β = E|Y|/d and σ = E|S_L|/d. Subadditivity, concavity of the binary entropy h, and Jensen for the perspective (t, m) ↦ t·h(m/t) give:
   - H(X) ≤ d·h(α);
   - H(Y|L) ≤ d(1−σ)·h(β/(1−σ));
   - and symmetrically H(Y) ≤ d·h(β), H(X|L) ≤ dσ·h(α/σ).
4. **Averaging.** Average the two identities. With g(a,t) = h(a) + t·h(a/t) and G(t) = max_a g(a,t), this gives (log₂N)/d ≤ ½[G(σ) + G(1−σ)] ≤ G(½), because G is concave.
5. **Value.** G(½) = h(⅓) + ½h(⅔) = (3/2)·log₂3 − 1. Hence N ≤ (3√3/2)^d. ∎

**Corollaries.**
- cov(d) ≥ 3^d/(3√3/2)^d = (2/√3)^d ≈ 1.1547^d.
- Every hyperplane {a·x + b·y = c} is an equality matrix, with labels u(x) = a·x and v(y) = c − b·y. So the bound also gives the effective exact-cover bound ec(D_n) ≥ (2/√3)^{n/2} ≈ 2^{0.104n} for the set D_n considered by [Diamond–Yehudayoff](https://eccc.weizmann.ac.il/report/2021/148/).
- **Prior work.**
  - Up to poly(n), this follows from the covering degree δ_OR(DISJ_1) = 2/√3 of [Alman–Li](https://arxiv.org/abs/2509.14489) (Thm C.2).
  - Jukna's earlier counting bound gives (3/2^{3/2})^d ≈ 1.06^d. Williams' "1.08^d" is a misquote of it.

**Sanity check.** `code/eqmax.py` computes the exact per-matrix maximum by MILP. For d = 2, 3, 4, 5 it gives 6, 14, 36, 86, against the bound 6.8, 17.5, 45.6, 118.4.

### 2. Upper bound (not refereed)

**Per type.** Fix the type (|x|, |y|) = (a, b) and a separator size s.

**One random matrix.**
1. Let F contain each s-set independently with probability q = 1/max(C(d−a, s−a), C(d−b, s)).
2. Each row x takes a random member of F that contains it.
3. Each column y takes a random member of F that avoids it.

A first-moment calculation shows that a fixed pair of the type is covered with probability ≥ 1/(8·R), where R = max(C(d−a, s−a), C(d−b, s)) / C(d−a−b, s−a).

**Covering the type.** O(R·d) random coordinate permutations of one good matrix then cover all pairs of the type.

**Bound.** Summing over types gives the explicit finite bound cov(d) ≤ (8d·ln3 + 8)·(d+1)²·max_{a,b} min_s R + (d+1)².

**Exponent.**
- At α = β = ⅓, σ = ½, the exponent of R is (2/3)·h(¼) − ⅓ = log₂(2/√3).
- A grid search shows that this is the max–min over all types.
- A closed-form proof of the max–min is not written out.

**Remark.** The known OV algorithms in time n·1.155^d (Nederlof–Węgrzycki STOC'21, Alman–Li FOCS'25) already reach this base. The only new point is that Williams' equality-matrix framework reaches it too.

### 3. Computations for small d

**Method.**
- `code/eqcover.py`: SAT encoding. Labels are WLOG separators S: rows x ⊆ S, columns y ⊆ [d]∖S.
- `code/sa_cover.c`: simulated annealing. One trick matters: WLOG matrix 0 covers (∅, ∅), so its row ∅ and column ∅ always share a label.

**Results.**
- cov(1..4) = 2, 2, 3, 4. Each value is certified by UNSAT at r − 1.
- cov(5) ≤ 5, and cov(6) ≤ 6 (Williams' value is reproduced).
- **cov(7) ≤ 8**: `code/covers/disj7_r8.txt`, checked by `python3 code/verify_cover.py code/covers/disj7_r8.txt`.
- For r = 7 at d = 7 the best annealing state leaves 5 of 2187 pairs uncovered. This is heuristic evidence that cov(7) = 8, not a proof.

### 4. The Diamond–Yehudayoff conjecture

**Conjecture** ([ECCC TR21-148](https://eccc.weizmann.ac.il/report/2021/148/)). If a hyperplane H ⊆ ℝ^n satisfies H ∩ {0,1}^n ⊆ D_n, then |H ∩ {0,1}^n| ≤ 2^{n/2}. If true it is sharp, and it would give ec(D_n) ≥ (3/2)^{n/2}.

**Equivalent form.** Every affine subspace V ⊆ ℝ^{2d} whose cube points are all disjoint pairs contains ≤ 2^d cube points. This holds because H ∩ cube = aff(H ∩ cube) ∩ cube, and a generic hyperplane through V avoids all other cube points.

**Checks.**
- `code/dy_affine.py` and `code/dy_affine.c` enumerate all such affinely closed sets.
- d = 2 gives max 4 (71 sets), and d = 3 gives max 8 (3942 sets). So the conjecture holds for d ≤ 3, over **all real weights**.
- Integer-weight searches up to d = 7 also never exceed 2^d.

**Where a proof gets stuck.**
- If some pair's projection of V is at most one-dimensional, S uses ≤ 2 states at that pair, and induction gives 2^d.
- The hard case is when every pair uses all three states (0, x, y).
- A "pairwise affine hull" induction lemma fails in 132 of 5850 such cases at d = 3.

### 5. A folklore remark on the inner-product-zero set

For Z_n = {(x,y) : ⟨x,y⟩ ≡ 0 mod 2}:
- every rectangle of a hyperplane inside Z_n is monochromatic for inner product, so Lindsey's lemma gives ≤ 2^{n/2} points per rectangle;
- Cauchy–Schwarz then gives ≤ 2^{3n/4} points per hyperplane;
- hence ec(Z_n) ≥ 2^{n/4−1}.

This is the argument of Jukna (CPC 2006, Cor. 3.10) for fat matchings, combined with Williams' observation (TR24-142, Thm 2) that exact-threshold gates are equality matrices. It is recorded here only as a corollary. For m = n/2 = 2, 3, 4, small-weight searches find at most 6, 12, 20 points per hyperplane.

---

## 中文

### 结论一览

| 命题 | 状态 | 位置 |
| --- | --- | --- |
| DISJ_d 内的单个等式矩阵至多含 (3√3/2)^d 个 1，故 cov(d) ≥ (2/√3)^d | 本文用熵方法证明。Alman–Li 的覆盖度在相差 poly(d) 的意义下已蕴含此结论，本文只是小幅改进 | §1 |
| cov(d) ≤ d^{O(1)}·(2/√3)^d | 本文证明了一个明确的有限界，未经审稿。指数由数值计算得到，max–min 的闭式证明尚未写出 | §2 |
| cov(7) ≤ 8，即 8^{1/7} ≈ 1.3459 < 6^{1/6} | 计算机找到的覆盖，已独立验证 | §3，`code/covers/disj7_r8.txt` |
| cov(7) ≤ 7 | 36 次退火均未找到（最好剩 5 对未覆盖），仍开放 | §3 |
| Diamond–Yehudayoff 猜想（含于 D_n 的超平面至多 2^{n/2} 个格点） | 对 d = n/2 ≤ 3 及所有实权重精确验证，一般情形开放 | §4 |
| 内积零集的超平面恰好覆盖 ec ≥ 2^{n/4−1} | 民间已知：Jukna 2006 Cor. 3.10 加上 Williams 2024 的「ETHR 门 = 等式矩阵」 | §5 |

**定义。**
- **DISJ_d** 是 2^d × 2^d 的矩阵：对 x, y ⊆ [d]，DISJ_d[x,y] = 1 当且仅当 x ∩ y = ∅，共有 3^d 个 1。
- **等式矩阵**（Williams，[ECCC TR24-142](https://eccc.weizmann.ac.il/report/2024/142/)）形如 M[x,y] = [u(x) = v(y)]。
- **cov(d)** 是最小的 t，使得 DISJ_d 等于 t 个等式矩阵的逐项 OR，且每个等式矩阵的 1 都落在 DISJ_d 的 1 之内。这样的 OR 是一种弱等式秩分解，所以 weak-eq-rank(DISJ_d) ≤ cov(d)。

### 1. 下界

**引理。** DISJ_d 内的任一等式矩阵 M 至多含 (3√3/2)^d 个 1。

*证明。*
1. **设定。** 令 (X, Y) 在 M 的 N 个 1 上均匀分布，标签 L = u(X) = v(Y)。对每个标签 ℓ，令 S_ℓ 为标签为 ℓ 的行之并；标签为 ℓ 的每一列都与 S_ℓ 不相交。
2. **两个恒等式。** 给定 L 时 (X, Y) 在一个矩形上均匀分布，且 L 既是 X 的函数也是 Y 的函数。因此 log₂N = H(X) + H(Y|L) = H(Y) + H(X|L)。
3. **熵估计。** 令 α = E|X|/d，β = E|Y|/d，σ = E|S_L|/d。由次可加性、二元熵 h 的凹性，以及透视函数 (t, m) ↦ t·h(m/t) 上的 Jensen 不等式：
   - H(X) ≤ d·h(α)；
   - H(Y|L) ≤ d(1−σ)·h(β/(1−σ))；
   - 对称地，H(Y) ≤ d·h(β)，H(X|L) ≤ dσ·h(α/σ)。
4. **平均。** 把两个恒等式平均。记 g(a,t) = h(a) + t·h(a/t)，G(t) = max_a g(a,t)，由 G 的凹性得 (log₂N)/d ≤ ½[G(σ) + G(1−σ)] ≤ G(½)。
5. **取值。** G(½) = h(⅓) + ½h(⅔) = (3/2)·log₂3 − 1，所以 N ≤ (3√3/2)^d。∎

**推论。**
- cov(d) ≥ 3^d/(3√3/2)^d = (2/√3)^d ≈ 1.1547^d。
- 超平面 {a·x + b·y = c} 本身是一个等式矩阵，标签为 u(x) = a·x，v(y) = c − b·y。所以对 [Diamond–Yehudayoff](https://eccc.weizmann.ac.il/report/2021/148/) 研究的集合 D_n，上述界也给出常数明确的恰好覆盖下界 ec(D_n) ≥ (2/√3)^{n/2} ≈ 2^{0.104n}。
- **已有工作。**
  - 在相差 poly(n) 的意义下，这可由 [Alman–Li](https://arxiv.org/abs/2509.14489) 的覆盖度 δ_OR(DISJ_1) = 2/√3（Thm C.2）推出。
  - Jukna 早先的计数界是 (3/2^{3/2})^d ≈ 1.06^d；Williams 写的「1.08^d」是对它的误引。

**数值核对。** `code/eqmax.py` 用 MILP 计算单个矩阵的精确最大值：d = 2, 3, 4, 5 时为 6、14、36、86，对应的理论界为 6.8、17.5、45.6、118.4。

### 2. 上界（未经审稿）

**按型处理。** 固定型 (|x|, |y|) = (a, b) 以及分隔集的大小 s。

**一个随机矩阵。**
1. 让 F 以概率 q = 1/max(C(d−a, s−a), C(d−b, s)) 独立地包含每个 s 元集。
2. 每一行 x 随机选取 F 中一个包含 x 的成员作为标签。
3. 每一列 y 随机选取 F 中一个与 y 不相交的成员作为标签。

一阶矩计算表明，该型中任一固定的对被覆盖的概率 ≥ 1/(8·R)，其中 R = max(C(d−a, s−a), C(d−b, s)) / C(d−a−b, s−a)。

**覆盖整个型。** 对一个好的矩阵再做 O(R·d) 次随机坐标置换，即可覆盖该型的所有对。

**界。** 对所有型求和，得到明确的有限界 cov(d) ≤ (8d·ln3 + 8)·(d+1)²·max_{a,b} min_s R + (d+1)²。

**指数。**
- 在 α = β = ⅓，σ = ½ 处，R 的指数为 (2/3)·h(¼) − ⅓ = log₂(2/√3)。
- 网格搜索显示这就是所有型上的 max–min。
- max–min 的闭式证明尚未写出。

**注记。** 已知的 OV 算法 n·1.155^d（Nederlof–Węgrzycki STOC'21，Alman–Li FOCS'25）已经达到这个底数；新的一点只是 Williams 的等式矩阵框架也能达到。

### 3. 小 d 的计算

**方法。**
- `code/eqcover.py`：SAT 编码，标签不妨取为分隔集 S，行 x ⊆ S，列 y ⊆ [d]∖S。
- `code/sa_cover.c`：模拟退火。关键技巧是：不妨设矩阵 0 覆盖 (∅, ∅)，于是让它的行 ∅ 与列 ∅ 始终共用同一个标签。

**结果。**
- cov(1..4) = 2、2、3、4，每个值都由 r − 1 时的 UNSAT 确认。
- cov(5) ≤ 5，cov(6) ≤ 6（复现了 Williams 的结果）。
- **cov(7) ≤ 8**：见 `code/covers/disj7_r8.txt`，用 `python3 code/verify_cover.py code/covers/disj7_r8.txt` 独立验证。
- d = 7、r = 7 时，退火的最好状态在 2187 对中仍剩 5 对未覆盖。这是 cov(7) = 8 的启发式证据，不是证明。

### 4. Diamond–Yehudayoff 猜想

**猜想**（[ECCC TR21-148](https://eccc.weizmann.ac.il/report/2021/148/)）。若超平面 H ⊆ ℝ^n 满足 H ∩ {0,1}^n ⊆ D_n，则 |H ∩ {0,1}^n| ≤ 2^{n/2}。若成立则是紧的，并可推出 ec(D_n) ≥ (3/2)^{n/2}。

**等价形式。** 任何所有格点都是不相交对的仿射子空间 V ⊆ ℝ^{2d}，至多含 2^d 个格点。理由是 H ∩ cube = aff(H ∩ cube) ∩ cube，而经过 V 的一般位置超平面会避开其余所有格点。

**验证。**
- `code/dy_affine.py` 与 `code/dy_affine.c` 枚举所有这样的仿射闭集。
- d = 2 时最大为 4（71 个集合），d = 3 时最大为 8（3942 个集合）。所以猜想对 d ≤ 3 及**所有实权重**成立。
- 整数权重搜索直到 d = 7，也从未超过 2^d。

**证明卡在哪里。**
- 若某一对坐标上 V 的投影至多一维，那么解集在这一对上至多用 2 种状态，归纳即得 2^d。
- 难点是每一对都用满三种状态（0、x、y）的情形。
- 在 d = 3 的 5850 个这类情形中，「两两仿射包」式的归纳引理失败 132 次。

### 5. 关于内积零集的民间结论

对 Z_n = {(x,y) : ⟨x,y⟩ ≡ 0 mod 2}：
- 含于 Z_n 的超平面所分解出的每个矩形关于内积都是单色的，由 Lindsey 引理，每个矩形至多 2^{n/2} 个点；
- 再用 Cauchy–Schwarz，每个超平面至多 2^{3n/4} 个点；
- 因此 ec(Z_n) ≥ 2^{n/4−1}。

这就是 Jukna（CPC 2006，Cor. 3.10）对 fat matching 的论证，加上 Williams（TR24-142，Thm 2）关于「精确阈值门是等式矩阵」的观察，这里只作为推论记录。m = n/2 = 2、3、4 时，小权重搜索找到的单个超平面最多含 6、12、20 个点。
