import ProblemQ.Uniform

/-!
# Theorem R3 with `y`-dependent centers

The only use of constant centers in Theorem R3 is that their level-3 part vanishes. Here each
member of the family may use its own center `c_a : (I → Bool) → ℝ`, an arbitrary function of the
live variables, as long as its (clipped) level-3 part has norm at most `ρ`. In the barrier regime
`ρ = n` is allowed, while the column's own level-3 vector has norm `≈ √(mQ) ≥ 9.4 n`. So a center
must carry a constant fraction of the column's level-3 energy to help.
-/

open Finset BigOperators
open scoped RealInnerProductSpace

namespace ProblemQ

noncomputable section

section Family

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool)

local notation "X" => colVec T I z

/-- Family bound with centers of small level-3 norm. -/
theorem family_cert_rho (ω : Fin m → Gate n T) {K : ℕ} (A : Fin K → Fin m → ℝ)
    (hA : ∀ a i, A a i = 1 ∨ A a i = -1)
    (h4 : ∀ i j k l : Fin m, i ≠ j → k ≠ l → ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∑ a, A a i * A a j * A a k * A a l = 0)
    (c : Fin K → (I → Bool) → ℝ) {W δ ρ : ℝ} (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hρ : ∀ a, ‖lvl3 (fun y => clip m (c a y))‖ ≤ ρ)
    (hS2 : 2 * (2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) + 2 * ρ ^ 2) ≤ S2c T I z ω) :
    ((univ.filter (fun a => certified T ω (A a) I z (c a) W δ)).card : ℝ)
        * S2c T I z ω ^ 2 ≤ 8 * K * Ux T I z ω := by
  classical
  set R2 : ℝ := W ^ 2 + 4 * δ * (m : ℝ) ^ 2 with hR2
  set Qa : Fin K → ℝ := fun a => ∑ p ∈ offPairs m, A a p.1 * A a p.2 * ⟪X (ω p.1), X (ω p.2)⟫
    with hQa
  have hS0 : 0 ≤ S2c T I z ω := by unfold S2c; positivity
  have hR0 : 0 ≤ R2 := by positivity
  have hcert : ∀ a, certified T ω (A a) I z (c a) W δ →
      S2c T I z ω ^ 2 / 4 ≤ Qa a ^ 2 := by
    intro a ha
    have hα : ∀ i, A a i = 1 ∨ A a i = -1 ∨ A a i = 0 := fun i => by
      rcases hA a i with h | h <;> simp [h]
    have hb := certified_ball T ω (A a) hα I z (c a) hW hδ ha
    set L := lvl3 (fun y => clip m (c a y))
    have hnorm : ‖∑ i, A a i • X (ω i)‖ ≤ Real.sqrt R2 + ρ := by
      have := norm_sub_norm_le (∑ i, A a i • X (ω i)) L
      linarith [hρ a]
    have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ a)
    have hb2 : ‖∑ i, A a i • X (ω i)‖ ^ 2 ≤ 2 * R2 + 2 * ρ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have h2 : Real.sqrt R2 ^ 2 = R2 := Real.sq_sqrt hR0
      nlinarith [sq_nonneg (Real.sqrt R2 - ρ)]
    rw [norm_sum_sq T I z ω (A a) (hA a)] at hb2
    have hQ : Qa a ≤ -(S2c T I z ω / 2) := by
      rw [show Qa a = ∑ p ∈ offPairs m, A a p.1 * A a p.2 * ⟪X (ω p.1), X (ω p.2)⟫ from rfl]
      linarith
    nlinarith
  have hsum := sum_family_Q_sq T I z ω A hA h4
  have hU : ∑ p ∈ offPairs m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2 ≤ Ux T I z ω := by
    rw [← sum_inner_sq]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => sq_nonneg _)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  calc ((univ.filter (fun a => certified T ω (A a) I z (c a) W δ)).card : ℝ)
        * S2c T I z ω ^ 2
      = 4 * ∑ a ∈ univ.filter (fun a => certified T ω (A a) I z (c a) W δ),
          S2c T I z ω ^ 2 / 4 := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * ∑ a ∈ univ.filter (fun a => certified T ω (A a) I z (c a) W δ), Qa a ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum
        intro a ha
        exact hcert a (by simpa using ha)
    _ ≤ 4 * ∑ a, Qa a ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => sq_nonneg _)
    _ = 4 * (2 * K * ∑ p ∈ offPairs m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2) := by
        rw [← hsum]
    _ ≤ 8 * K * Ux T I z ω := by nlinarith

end Family

section R3rho

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (W δ ρ : ℝ)

/-- A column is `ρ`-dangerous if some 4-wise independent `±1` family certifies it for half its
members, each member `a` using its own center `c_a(y)` whose clipped level-3 part has norm `≤ ρ`. -/
def dangerRho (ω : Fin m → Gate n T) (z : Fin n → Bool) : Prop :=
  ∃ (K : ℕ) (A : Fin K → Fin m → ℝ) (c : Fin K → (I → Bool) → ℝ), 0 < K ∧
    (∀ a i, A a i = 1 ∨ A a i = -1) ∧
    (∀ i j k l : Fin m, i ≠ j → k ≠ l → ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∑ a, A a i * A a j * A a k * A a l = 0) ∧
    (∀ a, ‖lvl3 (fun y => clip m (c a y))‖ ≤ ρ) ∧
    (K : ℝ) / 2 ≤ ((univ.filter (fun a => certified T ω (A a) I z (c a) W δ)).card : ℝ)

/-- Constant centers are the case `ρ = 0`. -/
lemma danger_rho_zero (ω : Fin m → Gate n T) (z : Fin n → Bool)
    (h : danger T I W δ ω z) : dangerRho T I W δ 0 ω z := by
  obtain ⟨K, A, c, hK, hA, h4, hhalf⟩ := h
  refine ⟨K, A, fun a _ => c a, hK, hA, h4, fun a => ?_, hhalf⟩
  rw [lvl3_const, norm_zero]

lemma good_not_danger_rho (ω : Fin m → Gate n T) (z : Fin n → Bool) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hN : (2048 : ℝ) < Fintype.card (L3 I))
    (hQ : 4096 ≤ m * Qm T I z ∧
      8 * (2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) + 2 * ρ ^ 2) ≤ m * Qm T I z)
    (hg : goodCol T I ω z) : ¬ dangerRho T I W δ ρ ω z := by
  rintro ⟨K, A, c, hK, hA, h4, hρ, hhalf⟩
  obtain ⟨hU, hS⟩ := hg
  set Q := Qm T I z
  set N : ℝ := (Fintype.card (L3 I) : ℝ)
  have hmQ : 0 < (m : ℝ) * Q := by linarith [hQ.1]
  have hS2 : 2 * (2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) + 2 * ρ ^ 2) ≤ S2c T I z ω := by
    linarith [hQ.2]
  have hfc := family_cert_rho T I z ω A hA h4 c hW hδ hρ hS2
  set cnt : ℝ := ((univ.filter (fun a => certified T ω (A a) I z (c a) W δ)).card : ℝ)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : cnt * (m * Q / 2) ^ 2 ≤ 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N)) := by
    have hc0 : 0 ≤ cnt := by positivity
    calc cnt * (m * Q / 2) ^ 2 ≤ cnt * S2c T I z ω ^ 2 := by
          gcongr
      _ ≤ 8 * K * Ux T I z ω := hfc
      _ ≤ 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N)) := by gcongr
  have hNpos : 0 < N := by linarith
  have h2 : cnt ≤ 512 * K * (1 / (m * Q) + 1 / N) := by
    have hm0 : (m : ℝ) ≠ 0 := by intro h; rw [h] at hmQ; simp at hmQ
    have hQ0 : Q ≠ 0 := by intro h; rw [h] at hmQ; simp at hmQ
    have e : 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N))
        = 512 * K * (1 / (m * Q) + 1 / N) * (m * Q / 2) ^ 2 := by
      field_simp; ring
    rw [e] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have h3 : 512 * K * (1 / (m * Q) + 1 / N) < K / 2 := by
    have a1 : 1 / (m * Q) ≤ 1 / 4096 := one_div_le_one_div_of_le (by norm_num) hQ.1
    have a2 : 1 / N < 1 / 2048 := one_div_lt_one_div_of_lt (by norm_num) hN
    nlinarith
  linarith

end R3rho

section UniformRho

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (W δ ρ : ℝ)

open Classical in
/-- **Theorem R3, uniform, with `y`-dependent centers of level-3 norm `≤ ρ`.** -/
theorem layering_barrier_uniform_rho (k : ℕ) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hN : 2048 < k.choose 3)
    (hQ : ∀ I : Finset (Fin n), I.card = k → ∀ z, 4096 ≤ m * Qm T I z ∧
      8 * (2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) + 2 * ρ ^ 2) ≤ m * Qm T I z)
    (hE : ∀ I : Finset (Fin n), I.card = k → ∀ z,
      (n.choose k : ℝ) * 2 ^ n * (4 * (k.choose 3 : ℝ) ^ 2
        * Real.exp (-(m * Qm T I z / (k.choose 3 : ℝ) ^ 2))) ≤ 1 / 2) :
    ((univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, dangerRho T I W δ ρ ω z)).card : ℝ)
      / (Fintype.card (Gate n T) : ℝ) ^ m ≤ 1 / 2 := by
  set G : ℝ := (Fintype.card (Gate n T) : ℝ) ^ m with hGdef
  have hG : 0 < G := by have := card_gate_pos T (n := n); positivity
  set P := (univ : Finset (Fin n)).powersetCard k
  have hcardL : ∀ I : Finset (Fin n), I.card = k → Fintype.card (L3 I) = k.choose 3 := by
    intro I hI; rw [card_L3]; simp [hI]
  have hsub : univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, dangerRho T I W δ ρ ω z)
      ⊆ P.biUnion (fun I => (univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω))) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    obtain ⟨I, hI, z, hd⟩ := hω
    refine mem_biUnion.mpr ⟨I, by simp [P, mem_powersetCard, hI], mem_biUnion.mpr
      ⟨z, mem_univ z, ?_⟩⟩
    simp only [mem_filter, mem_univ, true_and]
    intro ht
    have hNI : (2048 : ℝ) < Fintype.card (L3 I) := by rw [hcardL I hI]; exact_mod_cast hN
    have hpos : 0 < Fintype.card (L3 I) := by rw [hcardL I hI]; omega
    exact good_not_danger_rho T I W δ ρ ω z hW hδ hNI (hQ I hI z)
      (tight_good T I z hpos ω ht) hd
  have hP : (P.card : ℝ) = n.choose k := by
    simp [P, card_powersetCard]
  have hterm : ∀ I ∈ P, ∀ z : Fin n → Bool,
      ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ)
        ≤ G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) := by
    intro I hIP z
    have hI : I.card = k := (mem_powersetCard.mp hIP).2
    have hkn : k ≤ n := by
      have := card_le_univ I; rw [Fintype.card_fin] at this; omega
    have hch : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    have h16 : 16 ≤ Fintype.card (L3 I) := by rw [hcardL I hI]; omega
    have hc := card_not_tight T I z (m := m) h16
    rw [hcardL I hI] at hc
    have hE' := hE I hI z
    calc _ ≤ G * (4 * (k.choose 3 : ℝ) ^ 2
          * Real.exp (-(m * Qm T I z / (k.choose 3 : ℝ) ^ 2))) := hc
      _ ≤ G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          linarith
  have hsum : ((univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, dangerRho T I W δ ρ ω z)).card : ℝ) ≤ G / 2 := by
    calc _ ≤ ((P.biUnion (fun I => (univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ I ∈ P, (((univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω))).card : ℝ) := by
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ I ∈ P, ∑ z : Fin n → Bool,
          ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ) := by
          refine sum_le_sum (fun I _ => ?_)
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ I ∈ P, ∑ _z : Fin n → Bool, G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) :=
          sum_le_sum (fun I hI => sum_le_sum (fun z _ => hterm I hI z))
      _ = (P.card : ℝ) * (2 ^ n * (G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)))) := by
          simp [sum_const, Fintype.card_bool, nsmul_eq_mul]
      _ ≤ G / 2 := by
          rw [hP]
          rcases Nat.eq_zero_or_pos (n.choose k) with h0 | h0
          · rw [h0]; simp; positivity
          · have : (0 : ℝ) < n.choose k := by exact_mod_cast h0
            field_simp
            rfl
  rw [div_le_iff₀ hG]
  linarith

end UniformRho

section UniformRhoConcrete

variable {n m : ℕ}

open Classical in
/-- **Theorem R3, uniform, `y`-dependent centers, instantiated.** With `k = 2h+3`,
`N = C(k,3) > 2048`, `N² ≤ n`, `m ≥ 5800 (4⌊√n⌋+5) n²`, window `W ≤ n`, `4δm² ≤ n²` and centers
whose clipped level-3 part has norm `≤ n`: for at least half of all random circuits, no live set
`I` of size `k` and no column `z` is dangerous. -/
theorem layering_barrier_uniform_rho_concrete (h : ℕ) (hh : 1 ≤ h)
    (hN : 2048 < (2 * h + 3).choose 3) (hNn : ((2 * h + 3).choose 3) ^ 2 ≤ n)
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    {W δ ρ : ℝ} (hW0 : 0 ≤ W) (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2)
    (hρ0 : 0 ≤ ρ) (hρn : ρ ≤ n) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = 2 * h + 3 ∧ ∃ z, dangerRho (Tset n) I W δ ρ ω z)).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m ≤ 1 / 2 := by
  set N : ℝ := (((2 * h + 3).choose 3 : ℕ) : ℝ) with hNdef
  have hN0 : (2048 : ℝ) < N := by rw [hNdef]; exact_mod_cast hN
  have hNn' : N ^ 2 ≤ n := by rw [hNdef]; exact_mod_cast hNn
  have hn : (4000000 : ℝ) ≤ n := by nlinarith
  apply layering_barrier_uniform_rho (Tset n) W δ ρ (2 * h + 3) hW0 hδ0 hN
  · intro I hI z
    have key := mQ_ge h hh I hI z hm
    constructor
    · nlinarith
    · have : W ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hW0 hWn 2
      have : ρ ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hρ0 hρn 2
      nlinarith
  · intro I hI z
    -- identical exponent bookkeeping to `layering_barrier_uniform_concrete`
    have key := mQ_ge h hh I hI z hm
    have hNsq : 0 < N ^ 2 := by positivity
    have hexp : (90 : ℝ) * n ≤ m * Qm (Tset n) I z / N ^ 2 := by
      rw [le_div_iff₀ hNsq]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hE : Real.exp (-(m * Qm (Tset n) I z / N ^ 2)) ≤ Real.exp (-(90 * n)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hch : (n.choose (2 * h + 3) : ℝ) ≤ 2 ^ n := by
      exact_mod_cast Nat.choose_le_two_pow n (2 * h + 3)
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h4 : (2 : ℝ) ^ n * 2 ^ n ≤ Real.exp (2 * n) := by
      rw [← pow_add, show 2 * (n : ℝ) = ((n + n : ℕ) : ℝ) * 1 by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) h2e _
    have h8 : 8 * (n : ℝ) ≤ Real.exp (8 * n) := by linarith [Real.add_one_le_exp (8 * (n : ℝ))]
    have hprod : 8 * (n : ℝ) * (2 ^ n * 2 ^ n) ≤ Real.exp (90 * n) := by
      calc 8 * (n : ℝ) * (2 ^ n * 2 ^ n) ≤ Real.exp (8 * n) * Real.exp (2 * n) :=
            mul_le_mul h8 h4 (by positivity) (Real.exp_pos _).le
        _ = Real.exp (10 * n) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (90 * n) := Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp (90 * (n : ℝ)) * Real.exp (-(90 * n)) = 1 := by
      rw [← Real.exp_add]; simp
    have hEpos : 0 ≤ Real.exp (-(90 * (n : ℝ))) := (Real.exp_pos _).le
    calc (n.choose (2 * h + 3) : ℝ) * 2 ^ n * (4 * N ^ 2 * Real.exp (-(m * Qm (Tset n) I z / N ^ 2)))
        ≤ 2 ^ n * 2 ^ n * (4 * n * Real.exp (-(90 * n))) := by
          gcongr
      _ = (8 * (n : ℝ) * (2 ^ n * 2 ^ n)) * Real.exp (-(90 * n)) / 2 := by ring
      _ ≤ Real.exp (90 * n) * Real.exp (-(90 * n)) / 2 := by gcongr
      _ = 1 / 2 := by rw [hsplit]

end UniformRhoConcrete

end

end ProblemQ
