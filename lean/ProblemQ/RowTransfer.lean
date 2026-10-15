import Mathlib

/-!
# From restricted rows to full rows

`ProblemQ.TailDep` shows that rare coordinated firing in a column forces the *restricted* weight
vectors `a^I, b^I` (live coordinates only) to be nearly parallel. Clustering the weight matrix
sees the *full* rows. This file transfers correlation from restricted to full rows.

**Model.** Each coordinate `l < n` is live independently with probability `q`; a live set is
`b : Fin n → Bool`, with weight `wt q b = ∏ₗ (b l ? q : 1 - q)`.

For real rows `a, b` write `A = ‖a‖²`, `B = ‖b‖²`, `C = ⟨a,b⟩` and the restricted statistics
`S = ∑_{l live} aₗbₗ`, `Nₐ = ∑_{l live} aₗ²`, `N_b = ∑_{l live} bₗ²`. The spread parameters are
`κ_ab = ∑ aₗ²bₗ² / (AB)`, `κₐ = ∑ aₗ⁴ / A²`, `κ_b = ∑ bₗ⁴ / B²` (all `= 1/n` for `±1` rows).

* `var_lin`: `E[(∑ cₗ·1[l live] − q∑ cₗ)²] = q(1−q)∑ cₗ²` (exact second moment).
* `transfer`: for `0 < ε`, the live sets violating any of
  `S < q(C + ε√(AB))`, `q(1−ε)A < Nₐ`, `q(1−ε)B < N_b` have total weight at most
  `(1−q)/(q ε²) · (κ_ab + κₐ + κ_b)` (the first term is written with `√(AB)²`).
* `corr_of_good`: on the good event, if `ρ + ε ≥ 0` (with `ρ = C/√(AB)`) and `ε < 1`, then
  `S / √(Nₐ N_b) < (ρ + ε)/(1 − ε)`.
-/

open Finset Real

namespace ProblemQ

namespace RowTransfer

variable {n : ℕ}

/-- Probability of a single coordinate's state. -/
def pw (q : ℝ) (x : Bool) : ℝ := if x then q else 1 - q

/-- Weight of a live set. -/
def wt (q : ℝ) (b : Fin n → Bool) : ℝ := ∏ l, pw q (b l)

/-- `0/1` indicator of a bit. -/
def ind (x : Bool) : ℝ := if x then 1 else 0

lemma pw_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (x : Bool) : 0 ≤ pw q x := by
  cases x <;> simp [pw] <;> linarith

lemma wt_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Fin n → Bool) : 0 ≤ wt q b :=
  prod_nonneg (fun _ _ => pw_nonneg h0 h1 _)

/-- Expectations of product functions factor over coordinates. -/
lemma sum_wt_prod (q : ℝ) (f : Fin n → Bool → ℝ) :
    ∑ b : Fin n → Bool, wt q b * ∏ l, f l (b l) = ∏ l, ∑ x : Bool, pw q x * f l x := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl (fun b _ => ?_)
  rw [wt, ← prod_mul_distrib]

/-- Total weight `1`. -/
lemma sum_wt (q : ℝ) : ∑ b : Fin n → Bool, wt q b = 1 := by
  have h := sum_wt_prod (n := n) q (fun _ _ => 1)
  simp only [prod_const_one, mul_one] at h
  rw [h]
  simp [Fintype.sum_bool, pw]

/-- Centered indicator. -/
def cen (q : ℝ) (x : Bool) : ℝ := ind x - q

lemma sum_pw_cen (q : ℝ) : ∑ x : Bool, pw q x * cen q x = 0 := by
  simp [Fintype.sum_bool, pw, cen, ind]; ring

lemma sum_pw_cen_sq (q : ℝ) : ∑ x : Bool, pw q x * (cen q x * cen q x) = q * (1 - q) := by
  simp [Fintype.sum_bool, pw, cen, ind]; ring

lemma sum_pw_one (q : ℝ) : ∑ x : Bool, pw q x * 1 = 1 := by
  simp [Fintype.sum_bool, pw]

/-- `E[cen_l · cen_m] = q(1−q)·[l = m]`. -/
lemma cov_cen (q : ℝ) (l m : Fin n) :
    ∑ b : Fin n → Bool, wt q b * (cen q (b l) * cen q (b m))
      = if l = m then q * (1 - q) else 0 := by
  by_cases hlm : l = m
  · subst hlm
    have h := sum_wt_prod (n := n) q (fun i x => if i = l then cen q x * cen q x else 1)
    have hp : ∀ b : Fin n → Bool,
        ∏ i, (if i = l then cen q (b i) * cen q (b i) else 1) = cen q (b l) * cen q (b l) := by
      intro b; rw [prod_ite_eq' univ l]; simp
    simp only [hp] at h
    rw [h, if_pos rfl, ← mul_prod_erase univ _ (mem_univ l)]
    rw [prod_eq_one (fun i hi => by simp only [if_neg (ne_of_mem_erase hi), sum_pw_one]), mul_one]
    simp only [ite_true, sum_pw_cen_sq]
  · have h := sum_wt_prod (n := n) q
      (fun i x => if i = l then cen q x else if i = m then cen q x else 1)
    have hp : ∀ b : Fin n → Bool,
        ∏ i, (if i = l then cen q (b i) else if i = m then cen q (b i) else 1)
          = cen q (b l) * cen q (b m) := by
      intro b
      rw [← mul_prod_erase univ _ (mem_univ l), if_pos rfl,
        ← mul_prod_erase (univ.erase l) _ (mem_erase.mpr ⟨Ne.symm hlm, mem_univ m⟩),
        if_neg (Ne.symm hlm), if_pos rfl]
      rw [prod_eq_one (fun i hi => by
        have h1 : i ≠ m := ne_of_mem_erase hi
        have h2 : i ≠ l := ne_of_mem_erase (mem_of_mem_erase hi)
        rw [if_neg h2, if_neg h1]), mul_one]
    simp only [hp] at h
    rw [h, if_neg hlm, ← mul_prod_erase univ _ (mem_univ l)]
    simp only [ite_true, sum_pw_cen, zero_mul]

/-- **Exact second moment** of a restricted linear statistic. -/
theorem var_lin (q : ℝ) (c : Fin n → ℝ) :
    ∑ b : Fin n → Bool, wt q b * (∑ l, c l * ind (b l) - q * ∑ l, c l) ^ 2
      = q * (1 - q) * ∑ l, c l ^ 2 := by
  have hx : ∀ b : Fin n → Bool,
      (∑ l, c l * ind (b l) - q * ∑ l, c l) = ∑ l, c l * cen q (b l) := by
    intro b; simp only [cen, mul_sub, sum_sub_distrib]; rw [mul_comm q, sum_mul]
  simp_rw [hx, sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  have : ∀ l m : Fin n, ∑ b : Fin n → Bool, wt q b * (c l * cen q (b l) * (c m * cen q (b m)))
      = c l * c m * (if l = m then q * (1 - q) else 0) := by
    intro l m
    rw [← cov_cen q l m, mul_sum]
    refine sum_congr rfl (fun b _ => ?_); ring
  rw [sum_congr rfl (fun l _ => (sum_comm.trans (sum_congr rfl (fun m _ => this l m))))]
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
  refine sum_congr rfl (fun l _ => ?_); ring

/-- **Chebyshev.** The weight of `{b | λ ≤ |X b − q∑ c|}` is at most `q(1−q)∑ c²/λ²`. -/
theorem cheb_lin {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : Fin n → ℝ) {lam : ℝ} (hl : 0 < lam) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|), wt q b
      ≤ q * (1 - q) * (∑ l, c l ^ 2) / lam ^ 2 := by
  rw [← var_lin q c, sum_div, sum_filter]
  refine sum_le_sum (fun b _ => ?_)
  have hw := wt_nonneg h0 h1 b
  split_ifs with h
  · rw [le_div_iff₀ (by positivity)]
    have : lam ^ 2 ≤ (∑ l, c l * ind (b l) - q * ∑ l, c l) ^ 2 := by
      rw [← sq_abs (∑ l, c l * ind (b l) - q * ∑ l, c l)]
      exact pow_le_pow_left₀ hl.le h 2
    nlinarith
  · positivity

/-- `‖a‖²`. -/
def nsq (a : Fin n → ℝ) : ℝ := ∑ l, a l ^ 2

/-- `⟨a, c⟩`. -/
def dot (a c : Fin n → ℝ) : ℝ := ∑ l, a l * c l

/-- The good event: restricted inner product not too large, restricted norms not too small. -/
def Good (q ε : ℝ) (a c : Fin n → ℝ) (b : Fin n → Bool) : Prop :=
  ∑ l, a l * c l * ind (b l) < q * (dot a c + ε * Real.sqrt (nsq a * nsq c)) ∧
    q * (1 - ε) * nsq a < ∑ l, a l ^ 2 * ind (b l) ∧
    q * (1 - ε) * nsq c < ∑ l, c l ^ 2 * ind (b l)

/-- Chebyshev term rewritten with a relative deviation. -/
lemma cheb_rel {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) (c : Fin n → ℝ) {ε M : ℝ} (hε : 0 < ε)
    (hM : 0 < M) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => q * ε * M ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|),
        wt q b ≤ (1 - q) / (q * ε ^ 2) * ((∑ l, c l ^ 2) / M ^ 2) := by
  refine le_trans (cheb_lin h0.le h1 c (by positivity)) (le_of_eq ?_)
  field_simp

open Classical in
/-- **Transfer theorem.** The live sets outside `Good` have total weight at most
`(1−q)/(q ε²)·(κ_ac + κ_a + κ_c)`, with `κ_ac = ∑ aₗ²cₗ²/(AC)`, `κ_a = ∑ aₗ⁴/A²`,
`κ_c = ∑ cₗ⁴/C²`. -/
theorem transfer {q ε : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) (hε : 0 < ε) (a c : Fin n → ℝ)
    (ha : 0 < nsq a) (hc : 0 < nsq c) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => ¬ Good q ε a c b), wt q b
      ≤ (1 - q) / (q * ε ^ 2) *
        ((∑ l, (a l * c l) ^ 2) / Real.sqrt (nsq a * nsq c) ^ 2
          + (∑ l, (a l ^ 2) ^ 2) / nsq a ^ 2 + (∑ l, (c l ^ 2) ^ 2) / nsq c ^ 2) := by
  have hsq : 0 < Real.sqrt (nsq a * nsq c) := Real.sqrt_pos.mpr (mul_pos ha hc)
  have e1 := cheb_rel h0 h1 (fun l => a l * c l) hε hsq
  have e2 := cheb_rel h0 h1 (fun l => a l ^ 2) hε ha
  have e3 := cheb_rel h0 h1 (fun l => c l ^ 2) hε hc
  simp only [sum_filter] at e1 e2 e3 ⊢
  rw [mul_add, mul_add]
  refine le_trans ?_ (add_le_add (add_le_add e1 e2) e3)
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum (fun b _ => ?_)
  have hw := wt_nonneg h0.le h1 b
  by_cases hg : Good q ε a c b
  · rw [if_neg (not_not.mpr hg)]
    have : ∀ P : Prop, [Decidable P] → 0 ≤ (if P then wt q b else 0) := by
      intro P _; split_ifs <;> linarith
    linarith [this (q * ε * Real.sqrt (nsq a * nsq c)
        ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
      this (q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2|),
      this (q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2|)]
  · rw [if_pos hg]
    simp only [Good, not_and_or, not_lt] at hg
    have hnn : ∀ P : Prop, [Decidable P] → 0 ≤ (if P then wt q b else 0) := by
      intro P _; split_ifs <;> linarith
    rcases hg with h | h | h
    · have hT : q * ε * Real.sqrt (nsq a * nsq c)
          ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l| := by
        refine le_trans ?_ (le_abs_self _)
        have : dot a c = ∑ l, a l * c l := rfl
        rw [← this]; nlinarith
      rw [if_pos hT]
      linarith [hnn (q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2|),
        hnn (q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2|)]
    · have hT : q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2| := by
        rw [abs_sub_comm]
        refine le_trans ?_ (le_abs_self _)
        have : nsq a = ∑ l, a l ^ 2 := rfl
        rw [← this]; nlinarith
      rw [if_pos hT]
      linarith [hnn (q * ε * Real.sqrt (nsq a * nsq c)
          ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
        hnn (q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2|)]
    · have hT : q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2| := by
        rw [abs_sub_comm]
        refine le_trans ?_ (le_abs_self _)
        have : nsq c = ∑ l, c l ^ 2 := rfl
        rw [← this]; nlinarith
      rw [if_pos hT]
      linarith [hnn (q * ε * Real.sqrt (nsq a * nsq c)
          ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
        hnn (q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2|)]

/-- **On the good event the restricted correlation is at most `(ρ+ε)/(1−ε)`**, where
`ρ = ⟨a,c⟩/√(AC)` is the full-row correlation (assuming `ρ + ε ≥ 0`, `ε < 1`). -/
theorem corr_of_good {q ε : ℝ} (h0 : 0 < q) (hε1 : ε < 1) (a c : Fin n → ℝ)
    (ha : 0 < nsq a) (hc : 0 < nsq c) (b : Fin n → Bool) (hg : Good q ε a c b)
    (hρ : 0 ≤ dot a c / Real.sqrt (nsq a * nsq c) + ε) :
    (∑ l, a l * c l * ind (b l)) / Real.sqrt ((∑ l, a l ^ 2 * ind (b l)) * (∑ l, c l ^ 2 * ind (b l)))
      < (dot a c / Real.sqrt (nsq a * nsq c) + ε) / (1 - ε) := by
  obtain ⟨hS, hA, hC⟩ := hg
  set s := Real.sqrt (nsq a * nsq c) with hs
  set ρ := dot a c / s
  have hspos : 0 < s := Real.sqrt_pos.mpr (mul_pos ha hc)
  have h1e : 0 < 1 - ε := by linarith
  have hqe : 0 < q * (1 - ε) := mul_pos h0 h1e
  have hNa : 0 < ∑ l, a l ^ 2 * ind (b l) := lt_trans (by positivity) hA
  have hNc : 0 < ∑ l, c l ^ 2 * ind (b l) := lt_trans (by positivity) hC
  -- √(Nₐ N_c) > q(1−ε)·s
  have hprod : (q * (1 - ε)) ^ 2 * (nsq a * nsq c)
      < (∑ l, a l ^ 2 * ind (b l)) * (∑ l, c l ^ 2 * ind (b l)) := by
    have := mul_lt_mul'' hA hC (by positivity) (by positivity)
    nlinarith [this]
  have hN : q * (1 - ε) * s < Real.sqrt ((∑ l, a l ^ 2 * ind (b l)) * (∑ l, c l ^ 2 * ind (b l))) := by
    have e : q * (1 - ε) * s = Real.sqrt ((q * (1 - ε)) ^ 2 * (nsq a * nsq c)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hqe.le]
    rw [e]
    exact Real.sqrt_lt_sqrt (by positivity) hprod
  have hNpos : 0 < Real.sqrt ((∑ l, a l ^ 2 * ind (b l)) * (∑ l, c l ^ 2 * ind (b l))) :=
    lt_trans (by positivity) hN
  have hdot : dot a c = ρ * s := by simp only [ρ]; field_simp
  rw [div_lt_div_iff₀ hNpos h1e]
  have hS' : (∑ l, a l * c l * ind (b l)) < q * s * (ρ + ε) := by
    rw [hdot] at hS; linarith
  calc (∑ l, a l * c l * ind (b l)) * (1 - ε) < q * s * (ρ + ε) * (1 - ε) :=
        mul_lt_mul_of_pos_right hS' h1e
    _ = (ρ + ε) * (q * (1 - ε) * s) := by ring
    _ ≤ (ρ + ε) * Real.sqrt ((∑ l, a l ^ 2 * ind (b l)) * (∑ l, c l ^ 2 * ind (b l))) :=
        mul_le_mul_of_nonneg_left hN.le hρ

end RowTransfer

end ProblemQ
