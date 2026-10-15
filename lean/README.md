# ProblemQ — Lean 4 formalization of the oblivious window barrier (Theorem 3′)

Kernel-checked, no `sorry`, no `native_decide`, no custom axioms.
`#print axioms ProblemQ.barrier` reports only `propext`, `Classical.choice` and `Quot.sound`.
`leanchecker ProblemQ.Final` and `leanchecker --fresh ProblemQ.Final` (full kernel replay including Mathlib, 17 min) both exit with code 0. `leanchecker` also exits with code 0 on `ProblemQ.Layering`, `ProblemQ.Uniform` and `ProblemQ.Centers`; full `--fresh` replays of `ProblemQ.Layering` (21m47s) and `ProblemQ.Centers` (17m52s, covering everything) also exit 0.

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (see `lake-manifest.json`).

## Main theorem — `ProblemQ.barrier` (`ProblemQ/Final.lean`)

Fix `k = 2h + 3` with `h ≥ 1`, and let `N = C(k,3)`.

**Random circuit.** The circuit has `m` independent uniform gates `(w, t)`, where `w ∈ {±1}^n` and `t ∈ [-r, r]` with `r = 2(⌊√n⌋ + 1)`. Each gate computes `1[t ≤ ⟨w, x̃⟩]`.

**Oblivious list.** The list is fixed before the circuit. It has `L ≤ 2^k` entries, and each entry has:
- a coefficient vector `α_a ∈ {1, -1, 0}^m` with `|supp α_a| ≥ m/2`;
- center rules `c_a(I) : {0,1}^I → ℝ`.

**Certification.** A column `(I, z)` is certified by entry `a` if, for at most a `δ` fraction of `y ∈ {0,1}^I`,
`|Σ_i α_a,i · gate_i(merge I z y) − c_a(I)(y)| > W`.
The list *succeeds* on a circuit if some `I` with `|I| = k` has at least half of its columns certified by some entry.

**Hypotheses.**
- `8 N² ≤ n²`
- `8 (2n)^k ≤ e^N`
- `m ≥ 5800 (4⌊√n⌋ + 5) n²`
- `0 < W ≤ n`
- `4 δ m² ≤ n²`

**Conclusion.** The list succeeds on at most half of all circuits.

## Corollaries

- **`ProblemQ.barrier_bound`.** The explicit success probability is at most `4 (2n)^k e^{-C(k,3)}`.
- **`ProblemQ.barrier_family` (bounded-information adaptivity).** The list may be selected *after seeing the circuit* from a family of `F` lists fixed in advance. If `8 F (2n)^k ≤ e^{C(k,3)}`, no list of the family succeeds on at least half of the circuits.

## Theorem R3 — `ProblemQ.layering_barrier_concrete` (`ProblemQ/Layering.lean`)

Fix a live set `I` with `|I| = k = 2h+3` and `C(k,3) > 2048`.

**Danger.** A column is *dangerous* if some `K`-element family `{α_a} ⊂ {±1}^m` certifies it, with `y`-constant centers, for at least half of its members. The family must be 4-wise independent, meaning `Σ_a α_iα_jα_kα_l = 0` unless the indices pair up. Both the family and the centers may depend arbitrarily on the circuit and on the column.

**Statement.** For at least half of all random circuits, fewer than a quarter of the columns are dangerous.

**Hypotheses.**
- `n ≥ 7`
- `m ≥ 5800 (4⌊√n⌋+5) n²`
- `W ≤ n`
- `4 δ m² ≤ n²`

**Why this matters.** CTW's layerings are `n^{ε/200}`-wise independent with constant shifts. So even an adaptive choice of the layering family does not extend their correctness argument past `Θ(n^{2.5})`.

## Theorem R3, uniform — `ProblemQ.layering_barrier_uniform_concrete` (`ProblemQ/Uniform.lean`)

The live set is no longer fixed. Every entry `Z_{SS'} = Σ_i X_{iS} X_{iS'}` of the empirical level-3 Gram matrix gets a Chernoff–Bernstein tail:
- off-diagonal entries: `exp(−mQ/N²)`;
- diagonal entries: `exp(−mQ/(16N))`.

So a column fails to be "tight" with probability at most `4N² e^{−mQ/N²}`. This beats the `C(n,k)·2ⁿ` restrictions, which allows a union bound over all of them.

**Statement.** Under the same hypotheses as R3, plus `C(k,3)² ≤ n`: for at least half of all random circuits, **no** restriction `(I, z)` with `|I| = k` is dangerous. The live set and the column may be chosen after seeing the circuit.

## Theorem R3 with `y`-dependent centers — `ProblemQ.layering_barrier_uniform_rho_concrete` (`ProblemQ/Centers.lean`)

Each family member `a` may use its own center `c_a : {0,1}^I → ℝ`, an arbitrary function of the live variables. The only requirement is that the level-3 part of its clipped version has norm `≤ ρ`, with `ρ ≤ n`. Constant centers are the case `ρ = 0` (`danger_rho_zero`).

**Statement.** The conclusion of the uniform theorem still holds.

**Interpretation.** The column's own level-3 vector has norm about `√(mQ) ≥ 9.4 n`. So a center helps only if it carries a constant fraction of the column's level-3 energy, that is, only if it actually computes the live gates' level-3 contribution.

## Theorem NL-U — `ProblemQ.NLU.nl_u` (`ProblemQ/NLMain.lean`)

This is the barrier against **arbitrary non-linear** list approximations, uniform over all live sets.

**Model.** The circuit has `m` i.i.d. uniform gates `(w, t) ∈ {0,1}^n × [-rad, rad]`. Gates use `{0,1}` inputs: a gate outputs `1[t ≤ Σ_{x_l=1} ±1]`.

**Template.** The list is oblivious, with `L` entries `P a : literals → gate vector → Fin (m+1) → F₂`. Each output has F₂-degree `≤ d` in the gate variables and may depend arbitrarily on the literals.

**Success.** `Succeeds (hotP P) δ ω I` means that at least half of the columns of `I` have an entry that outputs `1hotSUM` of the gates correctly at all but a `δ` fraction of the column's points. `Succeeds` is generic in a Boolean correctness predicate; `hotP P` is the `1hotSUM` one.

**Hypotheses.**
- `16 M² ≤ s`
- `M s ≤ k`
- `F₀ ≤ m π₀/2`, where `π₀ = (3/5)/(2 rad + 1)`
- `δ M ≤ 1/100`
- `n - k ≥ 400`
- `20 q ≤ n - k`

**Conclusion.**
`#{ω : ∃ I, |I| = k, Succeeds (hotP P) δ ω I} ≤ C(n,k) · (50/3) · (M e^{-mπ₀/16} + C(n,q) (L (½ + (d+1)/√F₀)^M)^q) · |Gate|^m`.

**Verification.** `leanchecker ProblemQ.NLMain` and `leanchecker --fresh ProblemQ.NLMain` (full replay, 17m40s) both exit 0.

**Proof outline**:
- two-level frames, with rows on outside zeros and private gate blocks inside a row;
- Smolensky at the median, restricted to the private coins;
- independent blocks inside a row and independent rows across a frame;
- Chernoff typicality, with the private-gate density obtained by Bonferroni, Chebyshev and a signed binomial count;
- reverse Markov from "succeeds" to good frames;
- a union over `I`.

## Generic form and Theorem NL-SYM — `ProblemQ.NLU.nl_gen`, `ProblemQ.NLU.nl_sym` (`ProblemQ/NLMain.lean`, `ProblemQ/NLSym.lean`)

**Generic form.** The NL-U pipeline is stated for any Boolean correctness predicate `P a y u`, given a per-point bound `PointBound P F₀ p₀`. The bound says that once `≥ F₀` gates carry fair coins and the rest are fixed, each entry is correct for at most a `p₀` fraction of the coins. `nl_gen` gives the NL-U bound with `½ + (d+1)/√F₀` replaced by `p₀`.
- `nl_u` is `nl_gen` with `pointBound_hot`, which is Smolensky at the median.
- `nl_sym` is `nl_gen` with `pointBound_sym`, which is Lemma PS.

**NL-SYM.**
- Template: each entry is one polynomial `P a y : {0,1}^m → F₂` of degree `≤ d` for every point `y`.
- Correctness (`symP h P`): it outputs the fixed bit `⌊|u|/h⌋ mod 2` of the gate vector `u`. For `h = 2^t` this is `SYM_t = bit_t`.

**Hypotheses.** Same as NL-U, except:
- `h ≥ 1024` and `200 (d + 1) ≤ h`;
- `2600 h² ≤ F₀` replaces `1 ≤ F₀` (and still `F₀ ≤ m π₀/2`).

**Conclusion.** `#{ω : ∃ I, |I| = k, Succeeds (symP h P) δ ω I} ≤ C(n,k) · (50/3) · (M e^{-mπ₀/16} + C(n,q) (L · 0.93^M)^q) · |Gate|^m`.

**Verification.**
- `nl_sym`, `nl_u` and `nl_gen` depend only on the three standard axioms.
- `leanchecker ProblemQ.NLSym` exits 0; `leanchecker --fresh ProblemQ.NLSym` (full replay, 17m27s) also exits 0.

## Explicit instances and non-vacuity — `ProblemQ/NLBarrier.lean`

The bounds of `nl_gen` are shown to be at most **half of all circuits** for explicit parameters (`s = 16M²`, `q = ⌊(n−k)/20⌋`).

**`nl_half` (generic), `nl_u_half`, `nl_sym_half`.** Hypotheses:
- `L p₀^M ≤ 2^{-40}`, where `p₀ = 3/5` for `1hotSUM` with `F₀ = 100(d+1)²`, and `p₀ = 93/100` for the fixed bit with `F₀ = 2600h²`;
- `16M³ ≤ k`;
- `k + 400 ≤ n`;
- `n^k 2^{2k+45} ≤ 2^n`;
- `m ≥ 27(4√n+5)(k ln n + ln M + 5)`;
- `m ≥ (10/3)(4√n+5)F₀`;
- `0 ≤ δ` and `δM ≤ 1/100`.

Conclusion: `#{ω : ∃ I, |I| = k, Succeeds} ≤ ½ |Gate|^m`.

**`nl_eventually`, `nl_u_eventually`, `nl_sym_eventually`.**
- For every `d`, `L` (and `h`), there are constants `k, M, N₀` such that the conclusion holds for all `n ≥ N₀` and all `m` above the two thresholds.
- `M` comes from `p₀^M → 0`. `N₀` comes from `n^k/2^n → 0` (Mathlib's `tendsto_pow_const_div_const_pow_of_one_lt`).
- So the barrier theorems are not vacuous.

**Verification.** All five theorems depend only on the three standard axioms, and `leanchecker ProblemQ.NLBarrier` exits 0; `leanchecker --fresh ProblemQ.NLBarrier` (full replay, 17m26.548s) also exits 0.

## Lemma PS (periodic Smolensky) — `ProblemQ.Periodic.periodic_smolensky` (`ProblemQ/Periodic.lean`)

Target `bitAt h K c = ⌊(K + c)/h⌋ mod 2`; for `h = 2^t` this is `bit_t(K + c)`.

**Hypotheses.**
- `h ≥ 1024` (any integer; a power of two is not needed)
- `200 (d + 1) ≤ h`
- `F ≥ 2600 h²`
- `K ∈ ℕ` (no loss: the target depends only on `K mod 2h`)
- `Q ∈ V d` on `{0,1}^F`

**Conclusion.** `#{β : Q β = bitAt h K |β|} ≤ (93/100) · 2^F`.

**Proof outline**:
- Split `β = (β', β'')` with `|β'| = 2a`, `a = ⌊h²/13⌋`.
- For each `β''`, if the transition nearest to `a` is within `g = ⌊h/5⌋`, the target is one (possibly complemented) threshold on a window of width `2h` (`bitAt_window`).
- The window's complement is a Chernoff tail (`card_high_le`, `card_low_le`); inside the window, offset Smolensky applies (`slice_bound`, `slice_real`).
- `|β''| ~ Bin(N)`. `binom_avg` compares the binomial average of any `[0,1]`-valued `h`-periodic function with its uniform mean, with error `≤ h·C(N,N/2)/2`. It uses only the unimodality of binomial coefficients (one-step shifts with positive-variation telescoping).
- The general pair form is `ps_pair`; the numeric instantiation (`E ≤ e⁻⁴ ≤ 1/54`, `p h ≤ 2.1`, `50 h C(N,N/2) ≤ 2^N`) gives `≤ 0.905 + 0.01 ≤ 0.93`.

**Verification.** `#print axioms` lists only the three standard axioms. `leanchecker ProblemQ.Periodic` exits 0. `leanchecker --fresh ProblemQ.Periodic` (full replay, 17m43s) also exits 0.

## NL-U at CTW scale — `ProblemQ.NLU.nl_u_ctw` (`ProblemQ/NLCtw.lean`)

This theorem fixes CTW's own growth rates:
- `k = ⌈n^{ε/10}⌉` live variables;
- lists with `ln L ≤ n^{ε/100}`;
- gate-degree `d ≤ n^{1-ε/6}`;
- frame size `M = ⌈2n^{ε/100}⌉ + 57`, with error `δ ≤ 1/(100M)`.

**Statement.** For every `0 < ε < 1` there is `N₀` such that for all `n ≥ N₀`, every `1hotSUM` list template succeeds on some live set of size `k` for at most half of all circuits with `m ≥ 6000 · n^{5/2 − ε/3}` gates.

This lies just above CTW's range `m ≤ n^{5/2 − ε}`, so the barrier is kernel-checked at exactly the scale of the algorithm it constrains.

**Proof.** The statement is derived from `nl_u_half`. The "eventually" side conditions are proved from Mathlib asymptotics: `isLittleO_log_rpow_atTop` and `tendsto_rpow_atTop`.

**Verification.** `nl_u_ctw` depends only on the three standard axioms, and `leanchecker ProblemQ.NLCtw` exits 0. `leanchecker --fresh ProblemQ.NLCtw` (full replay, 16m01s) also exits 0.

## Littlewood–Offord via Sperner — `ProblemQ.LO.*` (`ProblemQ/LittlewoodOfford.lean`)

This is the rigorous anti-concentration kernel of the CAPP route.

- **`card_window_le`.** If `f : Finset α → ℤ` is strictly monotone, then each level set is an antichain. By Mathlib's `IsAntichain.sperner`, a window `[c, c+Δ)` therefore contains at most `Δ · C(n, ⌊n/2⌋)` sets.
- **`window_prob_le`.** In probability form the window has mass at most `Δ / √n`, using `choose_half_sq_mul_le`.
- **`erdos_lo` (Erdős–Littlewood–Offord).** For nonzero integer weights `a`, at most `Δ · C(k, ⌊k/2⌋)` points `y ∈ {0,1}^k` have `∑ aᵢ yᵢ ∈ [c, c+Δ)`. The proof flips the coordinates with negative weight, which makes the sum strictly monotone in the set of ones.

**Verification.** All three depend only on the three standard axioms, and `leanchecker ProblemQ.LittlewoodOfford` exits 0; `leanchecker --fresh ProblemQ.LittlewoodOfford` (full replay, 15m54s) also exits 0.

## Fan-in below `n` cannot compute parity — `ProblemQ.FaninParity.not_parity` (`ProblemQ/FaninParity.lean`)

This shows that the restricted class "THR∘THR with bottom fan-in `< n`" is trivial for lower bounds, at every size.

- **Statement.** Take `n ≥ 1` and any number `m` of Boolean bottom functions `gᵢ`, each ignoring at least one coordinate, with arbitrary real top weights `α` and threshold `T`. Then `x ↦ [∑ αᵢ gᵢ(x) ≥ T]` differs from parity at some input.
- **Proof.** A function that ignores coordinate `j` is orthogonal to the parity character `χ`, because flipping `j` is a sign-reversing involution (`corr_zero`). So `∑ₓ H(x)χ(x) = 0` for `H = ∑ αᵢ gᵢ − T`. If the circuit computed parity, every term would be `≤ 0` and the term at `x = 0` would be `< 0`.

**Verification.** `not_parity` depends only on the three standard axioms, and `leanchecker ProblemQ.FaninParity` exits 0. `leanchecker --fresh ProblemQ.FaninParity` (full replay, 18m17s) also exits 0.

## Tail dependence of halfspaces — `ProblemQ.TailDep.*` (`ProblemQ/TailDep.lean`)

This is the rigorous core of the tail-dependence argument: rare coordinated firing forces near-parallel normal vectors. Everything is stated by counting points of `{±1}^k`, with no regularity assumption.

- **`card_ge_le` (Hoeffding, counting form).** For `T ≥ 0` and `‖a‖² > 0`: `#{y | T ≤ ⟨a,y⟩} ≤ 2^k · exp(−T²/(2‖a‖²))`. The proof factors the exponential moment over coordinates (`Fintype.prod_sum`), then applies `cosh x ≤ exp(x²/2)` and Markov.
- **`card_all_ge_le` (group tail dependence).** `#{y | ∀ g, t_g ≤ ⟨a_g,y⟩} ≤ 2^k · exp(−(∑ t_g)²/(2‖∑ a_g‖²))`, using `‖∑ a_g‖² = ∑_{g,h} ⟨a_g,a_h⟩`.
- **`card_pair_le`, `pair_corr_ge` (pairs).** For unit `a, b` with `ρ = ⟨a,b⟩ > −1`, the joint tail at height `t` has at most `2^k·exp(−t²/(1+ρ))` points. Hence, if the joint tail has density `p > 0`, then `t² ≤ (1+ρ)·log(1/p)`.

**Verification.** `card_all_ge_le` and `pair_corr_ge` depend only on the three standard axioms, and `leanchecker ProblemQ.TailDep` exits 0. `leanchecker --fresh ProblemQ.TailDep` (full replay, 15m44s) also exits 0.

## From restricted rows to full rows — `ProblemQ.RowTransfer.*` (`ProblemQ/RowTransfer.lean`)

Each coordinate is live independently with probability `q`, and a live set has weight `∏ₗ (q or 1−q)`. For real rows `a, c` let `A = ‖a‖²`, `C = ‖c‖²` and `ρ = ⟨a,c⟩/√(AC)`.

- **`var_lin` (exact second moment).** `E[(∑ cₗ·1[l live] − q∑ cₗ)²] = q(1−q)∑ cₗ²`. The proof factors expectations over coordinates (`sum_wt_prod`, `cov_cen`).
- **`cheb_lin`.** The Chebyshev bound for the same statistic.
- **`transfer`.** The live sets violating any of the following have total weight at most `(1−q)/(qε²)·(κ_ac + κ_a + κ_c)`:
  - `∑_{live} aₗcₗ < q(⟨a,c⟩ + ε√(AC))`,
  - `q(1−ε)A < ∑_{live} aₗ²`,
  - `q(1−ε)C < ∑_{live} cₗ²`.

  Here `κ_ac = ∑ aₗ²cₗ²/(AC)`, `κ_a = ∑ aₗ⁴/A²` and `κ_c = ∑ cₗ⁴/C²`. For `±1` rows each `κ` is `1/n`, so the bound is `3(1−q)/(kε²)` with `k = qn`.
- **`corr_of_good`.** On that good event, if `ρ + ε ≥ 0` and `ε < 1`, the restricted correlation satisfies `∑ aₗcₗ / √(∑ aₗ² · ∑ cₗ²) < (ρ + ε)/(1 − ε)` (sums over live coordinates).

**Verification.** `transfer`, `corr_of_good` and `var_lin` depend only on the three standard axioms, and `leanchecker ProblemQ.RowTransfer` exits 0. `leanchecker --fresh ProblemQ.RowTransfer` (full replay, 16m54s) also exits 0.

## Bernstein-type concentration under restriction — `ProblemQ.RowTransfer.*` (`ProblemQ/Bernstein.lean`)

This file upgrades `transfer` from second-moment to exponential strength. Write `X = ∑ cₗ(1[l live] − q)` with `|cₗ| ≤ 1` and `V = q∑cₗ²`.

- **`mgf_le`.** `E e^{θX} ≤ e^{θ²V}` for `|θ| ≤ 1`. Each factor `e^{−sq}(1 + q(eˢ−1))` is bounded by `exp(q(eˢ−1−s)) ≤ exp(qs²)`, via `add_one_le_exp` and Mathlib's `abs_exp_sub_one_sub_id_le`.
- **`tail_le`, `abs_tail_le`.** `Pr[X ≥ λ] ≤ exp(−λ²/(4V))` and `Pr[|X| ≥ λ] ≤ 2exp(−λ²/(4V))` for `0 ≤ λ ≤ 2V`.
- **`transfer_pm1`.** For `±1` rows, `0 < ε ≤ 2` and `k = qn`, the bad event of `Good` has probability at most `6·exp(−ε²k/4)`. A union bound over the `m²` pairs therefore needs only `k ≳ (4/ε²)·ln(6m²)`.

**Verification.** `transfer_pm1` and `abs_tail_le` depend only on the three standard axioms, and `leanchecker ProblemQ.Bernstein` exits 0. `leanchecker --fresh ProblemQ.Bernstein` (full replay, 17m50s) also exits 0.

## Exact-threshold reductions — `ProblemQ.Ethr.*` (`ProblemQ/EthrReductions.lean`)

These are the elementary steps behind `lb/ETHR_LOWER_BOUND.md`. That bound is a routine corollary of Chen–Tal–Wang, not a new result.

- **`ethr_split`.** `[E = 0] = [E ≥ 0] + [−E ≥ 0] − 1`.
- **`top_ethr_of_ethr`.** An ETHR∘ETHR circuit with s bottom gates equals an ETHR∘THR circuit with 2s bottom gates.
- **`and_eq_zero_iff`.** For `|Eⱼ| ≤ B`, `(∀ j, Eⱼ = 0) ↔ ∑ⱼ (2B+1)^j Eⱼ = 0`, i.e. `AND ∘ ETHR ⊆ ETHR`.
- **`parity_ethr`.** Parity is computed by ETHR∘ETHR.

**Verification.** All four depend only on the three standard axioms. `leanchecker ProblemQ.EthrReductions` exits 0, and `leanchecker --fresh` (full replay, 17m33s) also exits 0.

## Proof architecture

| File | Content |
|---|---|
| `Cube.lean` | characters on `{0,1}^ι`, orthogonality, Bessel |
| `Smoothing.lean` | small-ball bound for sums of independent bounded vectors (Gaussian smoothing via Mathlib's Gaussian Fourier integral; no CLT) |
| `Gates.lean` | twist substitution; level-3 covariance of random restricted gates is diagonal and bounded below |
| `Level3.lean` | exact level-3 coefficient of `1[Σ sgn ≥ 1]`: `−(C(2h,h)/4^h)/(4(h+1))`; central-binomial bound |
| `Circuit.lean` | circuit and column model; certification ⇒ small ball (with clipping); per-column bound |
| `Barrier.lean` | union over live sets and list entries, plus Markov |
| `Atom.lean` | Chebyshev lower bound `Pr[τ = 1] ≥ (3/4)/(2r+1)` |
| `Final.lean` | numeric instantiation; `barrier_bound`, `barrier_family` |
| `Layering.lean` | Theorem R3: symmetry, i.i.d. moments, 4-wise fourth-moment identity, Chebyshev/Markov |
| `Uniform.lean` | i.i.d. Chernoff–Bernstein tail; tight columns are good; union over all `(I, z)` |
| `Centers.lean` | `y`-dependent centers with level-3 norm `≤ ρ`; uniform barrier for them |
| `Smolensky.lean` | Smolensky's lemma over F₂ (median and arbitrary threshold) |
| `Rows.lean`, `Restrict.lean` | independent-events counting; central binomial; Smolensky probability form; degree-preserving restriction |
| `NLPoint.lean` | per-point bound for 1hotSUM entries; abstract row lemma |
| `NLModel.lean` | `{0,1}`-input gates; two-level frame; gate value at row points |
| `NLRow.lean` | independent blocks (induction); general-index rows lemma |
| `NLFrame.lean` | gate = (row weights, rest); block counting; per-row bound `L p₀^M` |
| `NLFixed.lean` | fixed base point: circuit decomposition, independent rows, Chernoff typicality |
| `NLTypical.lean` | private-gate density: sign orthogonality, Chebyshev, signed binomial count, Bonferroni |
| `NLMarginal.lean` | bad points `≤ δ 2ⁿ`; reverse Markov to many good frames |
| `NLFrame.lean` (`PointBound`) | abstract per-point bound used by the whole pipeline |
| `NLMain.lean` | block existence, double counting, union over `I`: **`nl_gen`**; instance **`nl_u`** (`1hotSUM`) |
| `NLSym.lean` | Lemma PS ⇒ `PointBound` for fixed `bit_t`: **`nl_sym`** |
| `NLCtw.lean` | NL-U at CTW's growth rates: **`nl_u_ctw`** (m ≥ 6000·n^{5/2−ε/3}) |
| `LittlewoodOfford.lean` | Erdős–Littlewood–Offord via Sperner: **`card_window_le`**, **`window_prob_le`**, **`erdos_lo`** |
| `EthrReductions.lean` | exact-threshold reductions: **`top_ethr_of_ethr`**, **`and_eq_zero_iff`**, **`parity_ethr`** |
| `Bernstein.lean` | Bernstein under restriction: **`mgf_le`**, **`abs_tail_le`**, exponential **`transfer_pm1`** |
| `RowTransfer.lean` | restricted vs full rows under random restriction: **`var_lin`**, **`transfer`**, **`corr_of_good`** |
| `TailDep.lean` | Hoeffding (counting form); group and pair tail dependence: **`card_all_ge_le`**, **`pair_corr_ge`** |
| `FaninParity.lean` | bottom fan-in `< n` ⇒ not parity, any size: **`not_parity`** |
| `NLBarrier.lean` | explicit parameters: ≤ ½ of circuits (`nl_half`, `nl_u_half`, `nl_sym_half`); non-vacuity for all large `n` (`*_eventually`) |
| `Periodic.lean` | Lemma PS: one-transition window, `±1` Chernoff tails, binomial averaging via unimodality, **`periodic_smolensky`** |

## Scope

This is a barrier against a **method**, not a CAPP hardness result. Random circuits are easy for CAPP by other means.

Not covered:
- circuit-dependent lists beyond the 4-wise independent layering families of R3;
- centers whose level-3 part has norm `> n`;
- live-set sizes with `C(k,3)² > n` in the uniform version;
- certificates that are not linear windows;
- non-coordinate restrictions;
- algorithms that do not batch-evaluate every list entry.

See the top-level `README.md` for context.
