import ProblemQ.NLSym

/-!
# Explicit instances of Theorems NL-U and NL-SYM

`nl_gen` bounds the number of circuits on which a list succeeds by an expression in
`n, m, k, M, q, L, p₀`. Here the parameters are fixed explicitly (`s = 16 M²`,
`q = ⌊(n-k)/20⌋`) and the expression is shown to be at most **half of all circuits** under
elementary conditions:

* `L p₀^M ≤ 2^{-40}` (the list is not too long compared to the frame size `M`);
* `16 M³ ≤ k`, `k + 400 ≤ n`, `n^k 2^{2k+45} ≤ 2^n`;
* `m ≥ 27 (4√n + 5)(k ln n + ln M + 5)` and `m ≥ (10/3)(4√n + 5) F₀`.

Instances: `nl_u_half` (`1hotSUM`, `F₀ = 100(d+1)²`, `p₀ = 3/5`) and `nl_sym_half`
(fixed `bit`, `F₀ = 2600 h²`, `p₀ = 93/100`).
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ}

lemma PointBound.mono {m L : ℕ} {P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool}
    {F₀ : ℕ} {p₀ p₁ : ℝ} (h : PointBound P F₀ p₀) (hp : p₀ ≤ p₁) : PointBound P F₀ p₁ :=
  fun a y Pset u₀ hc => (h a y Pset u₀ hc).trans (by gcongr)

/-- `π₀ n ≥ (3/5)/(4√n + 5)`. -/
lemma π₀_ge (n : ℕ) : (3 / 5) / (4 * Real.sqrt n + 5) ≤ π₀ n := by
  unfold π₀ rad
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  push_cast
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

lemma exp_neg_five_le : Real.exp (-5) ≤ 3 / 200 := by
  have h1 := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have : (200 / 3 : ℝ) ≤ Real.exp 5 := by
    rw [h5]
    have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h1.le 5
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 5) (by norm_num)]
  linarith

open Classical in
/-- **Explicit barrier from `nl_gen`.** Under the elementary conditions above, the list
succeeds on some live set of size `k` for at most half of all circuits. -/
theorem nl_half {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)
    {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    {k M : ℕ} {δ : ℝ} (hM : 1 ≤ M) (hx : (L : ℝ) * p₀ ^ M ≤ 1 / 2 ^ 40)
    (hk : 16 * M ^ 3 ≤ k) (hn : k + 400 ≤ n)
    (hnk : (n : ℝ) ^ k * 2 ^ (2 * k + 45) ≤ 2 ^ n)
    (hm1 : (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m)
    (hm2 : (4 * Real.sqrt n + 5) * (10 / 3) * F₀ ≤ m)
    (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds P δ ω I)).card : ℝ)
      ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  set q := (n - k) / 20 with hqdef
  have hq : 20 * q ≤ n - k := Nat.mul_div_le _ _
  have hq' : n - k < 20 * q + 20 := by omega
  have hsk : M * (16 * M ^ 2) ≤ k := by
    calc M * (16 * M ^ 2) = 16 * M ^ 3 := by ring
      _ ≤ k := hk
  -- quantities
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hD : (0 : ℝ) < 4 * Real.sqrt n + 5 := by positivity
  have hπ := π₀_ge n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmπ : m * ((3 / 5) / (4 * Real.sqrt n + 5)) ≤ m * π₀ n :=
    mul_le_mul_of_nonneg_left hπ hm0
  have hmπ' : m * ((3 / 5) / (4 * Real.sqrt n + 5)) = (3 / 5) * m / (4 * Real.sqrt n + 5) := by
    ring
  -- hF
  have hF : (F₀ : ℝ) ≤ m * π₀ n / 2 := by
    have : (F₀ : ℝ) ≤ (3 / 5) * m / (4 * Real.sqrt n + 5) / 2 := by
      rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have main := nl_gen P hP hp₀ (k := k) (M := M) (s := 16 * M ^ 2) (q := q) (δ := δ) le_rfl hsk
    hF hδ0 hδM (by omega) hq
  refine le_trans main ?_
  -- first term: C(n,k) M e^{-mπ₀/16} ≤ e^{-5}
  set E := k * Real.log n + Real.log M + 5 with hE
  have hE0 : 0 ≤ E := by positivity
  have hexp : m * π₀ n / 16 ≥ E := by
    have : (3 / 5) * m / (4 * Real.sqrt n + 5) ≥ 27 * (3 / 5) * E := by
      rw [ge_iff_le, le_div_iff₀ hD]; nlinarith
    nlinarith
  have hck : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hT1 : (n.choose k : ℝ) * (M * Real.exp (-(m * π₀ n / 16))) ≤ 3 / 200 := by
    have h1 : Real.exp (-(m * π₀ n / 16)) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-E) = Real.exp (-5) / ((n : ℝ) ^ k * M) := by
      rw [hE, show -(k * Real.log n + Real.log M + 5) = -5 - (k * Real.log n + Real.log M) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_log (by linarith : (0 : ℝ) < M),
        ← Real.log_pow, Real.exp_log (by positivity)]
    have hnk0 : (0 : ℝ) < (n : ℝ) ^ k * M := by positivity
    calc (n.choose k : ℝ) * (M * Real.exp (-(m * π₀ n / 16)))
        ≤ (n : ℝ) ^ k * (M * Real.exp (-E)) := by
          gcongr
    _ = Real.exp (-5) := by rw [h2]; field_simp
    _ ≤ 3 / 200 := exp_neg_five_le
  -- second term: C(n,k) C(n,q) (L p₀^M)^q ≤ 3/200
  have hT2 : (n.choose k : ℝ) * ((n.choose q : ℝ) * ((L : ℝ) * p₀ ^ M) ^ q) ≤ 3 / 200 := by
    have hcq : (n.choose q : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n q
    have hx0 : 0 ≤ (L : ℝ) * p₀ ^ M := by positivity
    have hxq : ((L : ℝ) * p₀ ^ M) ^ q ≤ (1 / 2 ^ 40) ^ q := pow_le_pow_left₀ hx0 hx q
    have hexpo : 2 * n ≤ 40 * q + (2 * k + 38) := by omega
    have hpow : (2 : ℝ) ^ (2 * n) ≤ 2 ^ (40 * q) * 2 ^ (2 * k + 38) := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h40 : ((1 : ℝ) / 2 ^ 40) ^ q = 1 / 2 ^ (40 * q) := by
      rw [div_pow, one_pow, ← pow_mul, mul_comm]
    calc (n.choose k : ℝ) * ((n.choose q : ℝ) * ((L : ℝ) * p₀ ^ M) ^ q)
        ≤ (n : ℝ) ^ k * (2 ^ n * (1 / 2 ^ (40 * q))) := by
          rw [← h40]; gcongr
      _ ≤ 3 / 200 := by
          have h2n : (2 : ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
          have h45 : (2 : ℝ) ^ (2 * k + 45) = 2 ^ (2 * k + 38) * 128 := by
            rw [show 2 * k + 45 = (2 * k + 38) + 7 by ring, pow_add]; norm_num
          have hq0 : (0 : ℝ) < 2 ^ (40 * q) := by positivity
          have hk0 : (0 : ℝ) < 2 ^ (2 * k + 38) := by positivity
          have hX0 : (0 : ℝ) ≤ (n : ℝ) ^ k * 2 ^ n := by positivity
          have hA : ((n : ℝ) ^ k * 2 ^ n * 128) * 2 ^ (2 * k + 38)
              ≤ 2 ^ (40 * q) * 2 ^ (2 * k + 38) := by
            calc ((n : ℝ) ^ k * 2 ^ n * 128) * 2 ^ (2 * k + 38)
                = ((n : ℝ) ^ k * 2 ^ (2 * k + 45)) * 2 ^ n := by rw [h45]; ring
              _ ≤ 2 ^ n * 2 ^ n := by gcongr
              _ = 2 ^ (2 * n) := h2n.symm
              _ ≤ _ := hpow
          have hC : (n : ℝ) ^ k * 2 ^ n * 128 ≤ 2 ^ (40 * q) := le_of_mul_le_mul_right hA hk0
          have e1 : (n : ℝ) ^ k * (2 ^ n * (1 / 2 ^ (40 * q)))
              = ((n : ℝ) ^ k * 2 ^ n) / 2 ^ (40 * q) := by ring
          rw [e1, div_le_div_iff₀ hq0 (by norm_num)]
          linarith
  -- combine
  have hG : (0 : ℝ) ≤ (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by positivity
  have e : (n.choose k : ℝ) * (50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
        (n.choose q : ℝ) * ((L : ℝ) * p₀ ^ M) ^ q) * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m))
      = 50 / 3 * ((n.choose k : ℝ) * (M * Real.exp (-(m * π₀ n / 16)))
          + (n.choose k : ℝ) * ((n.choose q : ℝ) * ((L : ℝ) * p₀ ^ M) ^ q))
        * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by ring
  rw [e]
  have : 50 / 3 * ((n.choose k : ℝ) * (M * Real.exp (-(m * π₀ n / 16)))
          + (n.choose k : ℝ) * ((n.choose q : ℝ) * ((L : ℝ) * p₀ ^ M) ^ q)) ≤ 1 / 2 := by
    linarith
  exact mul_le_mul_of_nonneg_right this hG

/-- Smolensky with `F₀ = 100(d+1)²` free coins: `p₀ = ½ + 1/10 = 3/5`. -/
lemma pointBound_hot_35 {m L d : ℕ}
    (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d) :
    PointBound (hotP P) (100 * (d + 1) ^ 2) (3 / 5) := by
  have hF₁ : 1 ≤ 100 * (d + 1) ^ 2 := by nlinarith [Nat.zero_le d]
  have hsq : Real.sqrt ((100 * (d + 1) ^ 2 : ℕ) : ℝ) = 10 * (d + 1) := by
    push_cast
    rw [show (100 : ℝ) * ((d : ℝ) + 1) ^ 2 = (10 * ((d : ℝ) + 1)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hp : 1 / 2 + (d + 1 : ℝ) / Real.sqrt ((100 * (d + 1) ^ 2 : ℕ) : ℝ) ≤ 3 / 5 := by
    rw [hsq]
    have : (d + 1 : ℝ) / (10 * (d + 1)) = 1 / 10 := by field_simp
    rw [this]; norm_num
  exact (pointBound_hot P hP hF₁).mono hp

open Classical in
/-- **NL-U, explicit.** A `1hotSUM` list of `L` polynomials of gate-degree `≤ d` succeeds on
some live set of size `k` for at most half of all circuits, once
`L (3/5)^M ≤ 2^{-40}`, `16 M³ ≤ k`, `k + 400 ≤ n`, `n^k 2^{2k+45} ≤ 2^n`,
`m ≥ 27 (4√n+5)(k ln n + ln M + 5)`, `m ≥ (1000/3)(4√n+5)(d+1)²` and `δ M ≤ 1/100`. -/
theorem nl_u_half {m L d : ℕ}
    (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d)
    {k M : ℕ} {δ : ℝ} (hM : 1 ≤ M) (hx : (L : ℝ) * (3 / 5) ^ M ≤ 1 / 2 ^ 40)
    (hk : 16 * M ^ 3 ≤ k) (hn : k + 400 ≤ n)
    (hnk : (n : ℝ) ^ k * 2 ^ (2 * k + 45) ≤ 2 ^ n)
    (hm1 : (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m)
    (hm2 : (4 * Real.sqrt n + 5) * (10 / 3) * (100 * (d + 1) ^ 2) ≤ m)
    (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (hotP P) δ ω I)).card : ℝ)
      ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  have hPB := pointBound_hot_35 P hP
  refine nl_half (hotP P) hPB (by norm_num) hM hx hk hn hnk hm1 ?_ hδ0 hδM
  push_cast; exact hm2

open Classical in
/-- **NL-SYM, explicit.** Same, for the fixed bit `⌊|u|/h⌋ mod 2` with `h ≥ 1024`,
`200(d+1) ≤ h`, `L (93/100)^M ≤ 2^{-40}` and `m ≥ (10/3)(4√n+5) · 2600 h²`. -/
theorem nl_sym_half {m L d h : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → ZMod 2)
    (hP : ∀ a x, P a x ∈ Smolensky.V d) (hh : 1024 ≤ h) (hd : 200 * (d + 1) ≤ h)
    {k M : ℕ} {δ : ℝ} (hM : 1 ≤ M) (hx : (L : ℝ) * (93 / 100) ^ M ≤ 1 / 2 ^ 40)
    (hk : 16 * M ^ 3 ≤ k) (hn : k + 400 ≤ n)
    (hnk : (n : ℝ) ^ k * 2 ^ (2 * k + 45) ≤ 2 ^ n)
    (hm1 : (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m)
    (hm2 : (4 * Real.sqrt n + 5) * (10 / 3) * (2600 * h ^ 2) ≤ m)
    (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (symP h P) δ ω I)).card : ℝ)
      ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  have hPB := pointBound_sym P hP hh hd (F₀ := 2600 * h ^ 2) le_rfl
  refine nl_half (symP h P) hPB (by norm_num) hM hx hk hn hnk hm1 ?_ hδ0 hδM
  push_cast; exact hm2

/-! ### Non-vacuity: the conditions hold for all large `n` -/

open Classical in
/-- For every per-point bound `p₀ < 1`, list length `L` and `F₀` there are constants `k, M, N₀`
such that for all `n ≥ N₀` and all `m ≥ m₀(n) = O(√n log n)` (and `m ≥ (10/3)(4√n+5) F₀`), every
list succeeds on some live set of size `k` for at most half of all circuits. -/
theorem nl_eventually (p₀ : ℝ) (hp₀ : 0 ≤ p₀) (hp₁ : p₀ < 1) (L F₀ : ℕ) :
    ∃ k M N₀ : ℕ, 1 ≤ M ∧ ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ,
      (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m →
      (4 * Real.sqrt n + 5) * (10 / 3) * F₀ ≤ m →
      ∀ P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool, PointBound P F₀ p₀ →
      ∀ δ : ℝ, 0 ≤ δ → δ * M ≤ 1 / 100 →
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          ∃ I : Finset (Fin n), I.card = k ∧ Succeeds P δ ω I)).card : ℝ)
        ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (2 ^ 40 * ((L : ℝ) + 1)) by positivity) hp₁
  set M := M₀ + 1
  have hx : (L : ℝ) * p₀ ^ M ≤ 1 / 2 ^ 40 := by
    have h1 : p₀ ^ M ≤ p₀ ^ M₀ := pow_le_pow_of_le_one hp₀ hp₁.le (by omega)
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have h2 : (L : ℝ) * p₀ ^ M ≤ L * (1 / (2 ^ 40 * ((L : ℝ) + 1))) := by
      gcongr; linarith
    have h3 : (L : ℝ) * (1 / (2 ^ 40 * ((L : ℝ) + 1))) ≤ 1 / 2 ^ 40 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  set k := 16 * M ^ 3
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.1 ht).2 (1 / 2 ^ (2 * k + 45)) (by positivity))
  refine ⟨k, M, max N₁ (k + 400), by omega, fun n hn m hm1 hm2 P hP δ hδ0 hδM => ?_⟩
  have hnk : (n : ℝ) ^ k * 2 ^ (2 * k + 45) ≤ 2 ^ n := by
    have := hN₁ n (le_trans (le_max_left _ _) hn)
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at this
    exact this.le
  exact nl_half P hP hp₀ (by omega) hx le_rfl (le_trans (le_max_right _ _) hn) hnk hm1 hm2
    hδ0 hδM

open Classical in
/-- **NL-U is non-vacuous.** For every gate-degree `d` and list length `L` there are constants
`k, M, N₀` such that for all `n ≥ N₀` and `m ≥ max(27(4√n+5)(k ln n + ln M + 5),
(1000/3)(4√n+5)(d+1)²)`, every `1hotSUM` list of degree `≤ d` succeeds on some live set of size
`k` (with `δ ≤ 1/(100M)`) for at most half of all circuits. -/
theorem nl_u_eventually (d L : ℕ) :
    ∃ k M N₀ : ℕ, 1 ≤ M ∧ ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ,
      (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m →
      (4 * Real.sqrt n + 5) * (10 / 3) * (100 * (d + 1) ^ 2) ≤ m →
      ∀ P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2,
      (∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d) →
      ∀ δ : ℝ, 0 ≤ δ → δ * M ≤ 1 / 100 →
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (hotP P) δ ω I)).card : ℝ)
        ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  obtain ⟨k, M, N₀, hM, h⟩ := nl_eventually (3 / 5) (by norm_num) (by norm_num) L
    (100 * (d + 1) ^ 2)
  refine ⟨k, M, N₀, hM, fun n hn m hm1 hm2 P hP δ hδ0 hδM => ?_⟩
  exact h n hn m hm1 (by push_cast; exact hm2) (hotP P) (pointBound_hot_35 P hP) δ hδ0 hδM

open Classical in
/-- **NL-SYM is non-vacuous.** Same for the fixed bit `⌊|u|/h⌋ mod 2` (`h ≥ 1024`,
`200(d+1) ≤ h`), with `m ≥ (10/3)(4√n+5) · 2600 h²` in place of the `(d+1)²` condition. -/
theorem nl_sym_eventually (d L h : ℕ) (hh : 1024 ≤ h) (hd : 200 * (d + 1) ≤ h) :
    ∃ k M N₀ : ℕ, 1 ≤ M ∧ ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ,
      (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m →
      (4 * Real.sqrt n + 5) * (10 / 3) * (2600 * h ^ 2) ≤ m →
      ∀ P : Fin L → (Fin n → Bool) → (Fin m → Bool) → ZMod 2,
      (∀ a x, P a x ∈ Smolensky.V d) →
      ∀ δ : ℝ, 0 ≤ δ → δ * M ≤ 1 / 100 →
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (symP h P) δ ω I)).card : ℝ)
        ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  obtain ⟨k, M, N₀, hM, hmain⟩ := nl_eventually (93 / 100) (by norm_num) (by norm_num) L
    (2600 * h ^ 2)
  refine ⟨k, M, N₀, hM, fun n hn m hm1 hm2 P hP δ hδ0 hδM => ?_⟩
  exact hmain n hn m hm1 (by push_cast; exact hm2) (symP h P)
    (pointBound_sym P hP hh hd le_rfl) δ hδ0 hδM

end NLU

end

end ProblemQ
