import ProblemQ.RowTransfer

/-!
# Bernstein-type concentration under random restriction

`ProblemQ.RowTransfer.transfer` has second-moment strength: failure probability `O(1/(kε²))`.
This file upgrades it to exponential strength, which allows a union bound over all `m²` pairs of
gates once `k ≫ log m`.

Each coordinate is live independently with probability `q` (weights `wt q`). For a statistic
`X = ∑ cₗ(1[l live] − q)` with `|cₗ| ≤ 1` and `V = q ∑ cₗ²`:

* `mgf_le`: `E e^{θX} ≤ e^{θ² V}` for `|θ| ≤ 1`. Each factor is `e^{−sq}(1 + q(eˢ − 1))
  ≤ exp(q(eˢ − 1 − s)) ≤ exp(q s²)`, using `|eˢ − 1 − s| ≤ s²` for `|s| ≤ 1`.
* `tail_le`: `Pr[X ≥ λ] ≤ exp(−λ²/(4V))` for `0 ≤ λ ≤ 2V`.
* `abs_tail_le`: `Pr[|X| ≥ λ] ≤ 2 exp(−λ²/(4V))`.
* `transfer_pm1`: for `±1` rows the bad event of `RowTransfer.Good` has probability at most
  `6 exp(−ε² q n / 4)`, i.e. `6 e^{−ε²k/4}` with `k = qn`, for `0 < ε ≤ 2`. With `m` gates, a
  union bound over all pairs fails with probability at most `3 m² e^{−ε²k/4}`.
-/

open Finset Real

namespace ProblemQ

namespace RowTransfer

variable {n : ℕ}

/-- One coordinate: `E e^{s(1[live] − q)} ≤ e^{q s²}` for `|s| ≤ 1`. -/
lemma factor_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {s : ℝ} (hs : |s| ≤ 1) :
    ∑ x : Bool, pw q x * exp (s * cen q x) ≤ exp (q * s ^ 2) := by
  have hfac : ∑ x : Bool, pw q x * exp (s * cen q x) = exp (-(s * q)) * (1 + q * (exp s - 1)) := by
    simp only [Fintype.sum_bool, pw, cen, ind, if_true, if_false]
    simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [show s * (1 - q) = s + -(s * q) by ring, exp_add, show s * (0 - q) = -(s * q) by ring]
    ring
  rw [hfac]
  have hx : 0 ≤ 1 + q * (exp s - 1) := by
    have := exp_pos s; nlinarith
  calc exp (-(s * q)) * (1 + q * (exp s - 1))
      ≤ exp (-(s * q)) * exp (q * (exp s - 1)) := by
        gcongr; linarith [add_one_le_exp (q * (exp s - 1))]
    _ = exp (q * (exp s - 1 - s)) := by rw [← exp_add]; ring_nf
    _ ≤ exp (q * s ^ 2) := by
        gcongr
        have := abs_exp_sub_one_sub_id_le hs
        exact (le_abs_self _).trans this

/-- **Exponential moment.** `E e^{θX} ≤ e^{θ² V}` with `V = q ∑ cₗ²`, for `|θ| ≤ 1`, `|cₗ| ≤ 1`. -/
theorem mgf_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : Fin n → ℝ) (hc : ∀ l, |c l| ≤ 1)
    {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∑ b : Fin n → Bool, wt q b * exp (θ * ∑ l, c l * cen q (b l))
      ≤ exp (θ ^ 2 * (q * ∑ l, c l ^ 2)) := by
  have hprod : ∀ b : Fin n → Bool,
      exp (θ * ∑ l, c l * cen q (b l)) = ∏ l, exp ((θ * c l) * cen q (b l)) := by
    intro b; rw [mul_sum, exp_sum]; refine prod_congr rfl (fun l _ => ?_); ring_nf
  simp_rw [hprod]
  rw [sum_wt_prod q (fun l x => exp ((θ * c l) * cen q x))]
  calc ∏ l, ∑ x : Bool, pw q x * exp ((θ * c l) * cen q x)
      ≤ ∏ l, exp (q * (θ * c l) ^ 2) := by
        refine prod_le_prod₀ (fun l _ => ?_) (fun l _ => factor_le h0 h1 ?_)
        · exact sum_nonneg (fun x _ => mul_nonneg (pw_nonneg h0 h1 x) (exp_pos _).le)
        · rw [abs_mul]
          nlinarith [abs_nonneg θ, abs_nonneg (c l), hc l]
    _ = exp (θ ^ 2 * (q * ∑ l, c l ^ 2)) := by
        rw [← exp_sum]; congr 1; rw [mul_sum, mul_sum]
        refine sum_congr rfl (fun l _ => ?_); ring

/-- **Bernstein tail.** `Pr[X ≥ λ] ≤ exp(−λ²/(4V))` for `0 ≤ λ ≤ 2V`, `V = q∑cₗ² > 0`. -/
theorem tail_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : Fin n → ℝ) (hc : ∀ l, |c l| ≤ 1)
    (hV : 0 < q * ∑ l, c l ^ 2) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 2 * (q * ∑ l, c l ^ 2)) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)), wt q b
      ≤ exp (-(lam ^ 2 / (4 * (q * ∑ l, c l ^ 2)))) := by
  set V := q * ∑ l, c l ^ 2 with hVdef
  set θ := lam / (2 * V) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hl0 (by positivity)
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by positivity)]; exact hl1
  have habs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0]; exact hθ1
  have hm := mgf_le h0 h1 c hc habs
  -- Markov with `e^{θX}`.
  have hmark : (∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)), wt q b)
      * exp (θ * lam) ≤ ∑ b : Fin n → Bool, wt q b * exp (θ * ∑ l, c l * cen q (b l)) := by
    rw [sum_mul]
    calc ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)), wt q b * exp (θ * lam)
        ≤ ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)),
            wt q b * exp (θ * ∑ l, c l * cen q (b l)) := by
          refine sum_le_sum (fun b hb => ?_)
          simp only [mem_filter, mem_univ, true_and] at hb
          exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb hθ0))
            (wt_nonneg h0 h1 b)
      _ ≤ ∑ b : Fin n → Bool, wt q b * exp (θ * ∑ l, c l * cen q (b l)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun b _ _ => mul_nonneg (wt_nonneg h0 h1 b) (exp_pos _).le)
  have hpos : 0 < exp (θ * lam) := exp_pos _
  have key : θ ^ 2 * V - θ * lam = -(lam ^ 2 / (4 * V)) := by
    rw [hθ]; field_simp; ring
  calc ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)), wt q b
      ≤ exp (θ ^ 2 * V) / exp (θ * lam) := by
        rw [le_div_iff₀ hpos]; exact hmark.trans hm
    _ = exp (-(lam ^ 2 / (4 * V))) := by rw [← exp_sub, key]

/-- `∑ cₗ·1[l live] − q∑cₗ = ∑ cₗ(1[l live] − q)`. -/
lemma lin_cen (q : ℝ) (c : Fin n → ℝ) (b : Fin n → Bool) :
    ∑ l, c l * ind (b l) - q * ∑ l, c l = ∑ l, c l * cen q (b l) := by
  simp only [cen, mul_sub, sum_sub_distrib]; rw [mul_comm q, sum_mul]

/-- **Two-sided Bernstein.** `Pr[|∑ cₗ1[l live] − q∑cₗ| ≥ λ] ≤ 2 exp(−λ²/(4V))`. -/
theorem abs_tail_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (c : Fin n → ℝ) (hc : ∀ l, |c l| ≤ 1)
    (hV : 0 < q * ∑ l, c l ^ 2) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 2 * (q * ∑ l, c l ^ 2)) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|), wt q b
      ≤ 2 * exp (-(lam ^ 2 / (4 * (q * ∑ l, c l ^ 2)))) := by
  have hneg : ∀ l, |(-c) l| ≤ 1 := fun l => by simpa using hc l
  have hsq : ∑ l, (-c) l ^ 2 = ∑ l, c l ^ 2 := by simp
  have t1 := tail_le h0 h1 c hc hV hl0 hl1
  have t2 := tail_le h0 h1 (-c) hneg (by rw [hsq]; exact hV) hl0 (by rw [hsq]; exact hl1)
  rw [hsq] at t2
  have hsub : univ.filter (fun b : Fin n → Bool => lam ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|)
      ⊆ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l))
        ∪ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, (-c) l * cen q (b l)) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union] at hb ⊢
    rw [lin_cen] at hb
    have hn : ∑ l, (-c) l * cen q (b l) = -∑ l, c l * cen q (b l) := by
      simp [neg_mul, sum_neg_distrib]
    rw [hn]
    rcases le_abs'.mp hb with h | h
    · right; linarith
    · left; exact h
  calc ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|), wt q b
      ≤ ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l))
          ∪ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, (-c) l * cen q (b l)), wt q b :=
        sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => wt_nonneg h0 h1 b)
    _ ≤ ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)), wt q b
          + ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, (-c) l * cen q (b l)), wt q b :=
        by
          have h := sum_union_inter (s₁ := univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l)))
            (s₂ := univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, (-c) l * cen q (b l))) (f := wt q)
          have hi : 0 ≤ ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, c l * cen q (b l))
              ∩ univ.filter (fun b : Fin n → Bool => lam ≤ ∑ l, (-c) l * cen q (b l)), wt q b :=
            sum_nonneg (fun b _ => wt_nonneg h0 h1 b)
          linarith
    _ ≤ _ := by linarith

/-- Tail weight of a restricted linear statistic. -/
noncomputable def tailW (q : ℝ) (c : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∑ b ∈ univ.filter (fun b : Fin n → Bool => lam ≤ |∑ l, c l * ind (b l) - q * ∑ l, c l|), wt q b

open Classical in
/-- The bad event of `Good` is covered by the three tails. -/
lemma bad_le_three {q ε : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (a c : Fin n → ℝ) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => ¬ Good q ε a c b), wt q b
      ≤ tailW q (fun l => a l * c l) (q * ε * Real.sqrt (nsq a * nsq c))
        + tailW q (fun l => a l ^ 2) (q * ε * nsq a) + tailW q (fun l => c l ^ 2) (q * ε * nsq c) := by
  simp only [tailW, sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum (fun b _ => ?_)
  have hw := wt_nonneg h0 h1 b
  have hnn : ∀ P : Prop, [Decidable P] → 0 ≤ (if P then wt q b else 0) := by
    intro P _; split_ifs <;> linarith
  by_cases hg : Good q ε a c b
  · rw [if_neg (not_not.mpr hg)]
    linarith [hnn (q * ε * Real.sqrt (nsq a * nsq c)
        ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
      hnn (q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2|),
      hnn (q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2|)]
  · rw [if_pos hg]
    simp only [Good, not_and_or, not_lt] at hg
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
        rw [abs_sub_comm]; refine le_trans ?_ (le_abs_self _)
        have : nsq a = ∑ l, a l ^ 2 := rfl
        rw [← this]; nlinarith
      rw [if_pos hT]
      linarith [hnn (q * ε * Real.sqrt (nsq a * nsq c)
          ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
        hnn (q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2|)]
    · have hT : q * ε * nsq c ≤ |∑ l, c l ^ 2 * ind (b l) - q * ∑ l, c l ^ 2| := by
        rw [abs_sub_comm]; refine le_trans ?_ (le_abs_self _)
        have : nsq c = ∑ l, c l ^ 2 := rfl
        rw [← this]; nlinarith
      rw [if_pos hT]
      linarith [hnn (q * ε * Real.sqrt (nsq a * nsq c)
          ≤ |∑ l, a l * c l * ind (b l) - q * ∑ l, a l * c l|),
        hnn (q * ε * nsq a ≤ |∑ l, a l ^ 2 * ind (b l) - q * ∑ l, a l ^ 2|)]

/-- For a `±1` vector every square is `1`. -/
lemma sq_pm1 {x : ℝ} (hx : x = 1 ∨ x = -1) : x ^ 2 = 1 := by
  rcases hx with h | h <;> simp [h]

lemma abs_pm1 {x : ℝ} (hx : x = 1 ∨ x = -1) : |x| ≤ 1 := by
  rcases hx with h | h <;> simp [h]

open Classical in
/-- **Exponential transfer for `±1` rows.** For `0 < q ≤ 1`, `0 < ε ≤ 2` and `n ≥ 1`, the live
sets outside `Good q ε a c` have total weight at most `6 exp(−ε² q n / 4)`. -/
theorem transfer_pm1 {q ε : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hn : 1 ≤ n) (a c : Fin n → ℝ) (ha : ∀ l, a l = 1 ∨ a l = -1) (hc : ∀ l, c l = 1 ∨ c l = -1) :
    ∑ b ∈ univ.filter (fun b : Fin n → Bool => ¬ Good q ε a c b), wt q b
      ≤ 6 * exp (-(ε ^ 2 * (q * n) / 4)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : nsq a = n := by simp [nsq, sq_pm1 (ha _)]
  have hC : nsq c = n := by simp [nsq, sq_pm1 (hc _)]
  have hAC : ∑ l, (a l * c l) ^ 2 = n := by simp [mul_pow, sq_pm1 (ha _), sq_pm1 (hc _)]
  have hA2 : ∑ l, (a l ^ 2) ^ 2 = n := by simp [sq_pm1 (ha _)]
  have hC2 : ∑ l, (c l ^ 2) ^ 2 = n := by simp [sq_pm1 (hc _)]
  have hs : Real.sqrt (nsq a * nsq c) = n := by
    rw [hA, hC, Real.sqrt_mul_self hnr.le]
  have hV : 0 < q * (n : ℝ) := mul_pos h0 hnr
  have hl0 : 0 ≤ q * ε * (n : ℝ) := by positivity
  have hl1 : q * ε * (n : ℝ) ≤ 2 * (q * n) := by nlinarith
  have hexp : exp (-((q * ε * n) ^ 2 / (4 * (q * n)))) = exp (-(ε ^ 2 * (q * n) / 4)) := by
    congr 1; field_simp
  have t1 := abs_tail_le h0.le h1 (fun l => a l * c l)
    (fun l => by rw [abs_mul]; nlinarith [abs_pm1 (ha l), abs_pm1 (hc l), abs_nonneg (a l), abs_nonneg (c l)])
    (by rw [hAC]; exact hV) (lam := q * ε * n) hl0 (by rw [hAC]; exact hl1)
  have t2 := abs_tail_le h0.le h1 (fun l => a l ^ 2) (fun l => by rw [sq_pm1 (ha l)]; simp)
    (by rw [hA2]; exact hV) (lam := q * ε * n) hl0 (by rw [hA2]; exact hl1)
  have t3 := abs_tail_le h0.le h1 (fun l => c l ^ 2) (fun l => by rw [sq_pm1 (hc l)]; simp)
    (by rw [hC2]; exact hV) (lam := q * ε * n) hl0 (by rw [hC2]; exact hl1)
  rw [hAC, hexp] at t1; rw [hA2, hexp] at t2; rw [hC2, hexp] at t3
  have hb := bad_le_three (ε := ε) h0.le h1 a c
  rw [hs, hA, hC] at hb
  simp only [tailW] at hb
  linarith

end RowTransfer

end ProblemQ
