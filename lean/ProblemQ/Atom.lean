import ProblemQ.Barrier

/-!
# Lower bound on the atom probability `Pr[τ = 1]`

Thresholds are uniform on `T n = [-r, r] ∩ ℤ` with `r = 2 (⌊√n⌋ + 1)`.
By Chebyshev, `|outside| ≤ r - 1` for at least `3/4` of the outside weights, and then exactly
one threshold gives `τ = 1`. Hence `pAtom ≥ (3/4) / (2r + 1)`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

/-- Threshold range radius. -/
def rad (n : ℕ) : ℤ := 2 * ((Nat.sqrt n : ℤ) + 1)

/-- Threshold set. -/
def Tset (n : ℕ) : Finset ℤ := Finset.Icc (-rad n) (rad n)

instance (n : ℕ) : Nonempty (Tset n) := ⟨⟨0, by simp [Tset, rad]; constructor <;> positivity⟩⟩

variable {n : ℕ}

/-- Integer version of the outside sum. -/
def outsideZ (I : Finset (Fin n)) (z : Fin n → Bool) (w : {j // j ∉ I} → Bool) : ℤ :=
  ∑ j : {j // j ∉ I}, (if (w j == z j) = true then 1 else -1)

lemma outside_eq (I : Finset (Fin n)) (z : Fin n → Bool) (w : {j // j ∉ I} → Bool) :
    outside I z w = (outsideZ I z w : ℝ) := by
  unfold outside outsideZ
  push_cast
  refine sum_congr rfl (fun j _ => ?_)
  rw [sgn_mul_sgn]
  cases (w j == z j) <;> simp [sgn]

/-- Second moment of the outside sum. -/
lemma sum_outside_sq (I : Finset (Fin n)) (z : Fin n → Bool) :
    ∑ w : {j // j ∉ I} → Bool, outside I z w ^ 2
      = (Fintype.card {j // j ∉ I} : ℝ) * 2 ^ Fintype.card {j // j ∉ I} := by
  unfold outside
  simp_rw [sq, sum_mul_sum]
  rw [sum_comm]
  have : ∀ j : {j // j ∉ I}, ∑ w : {j // j ∉ I} → Bool, ∑ l : {j // j ∉ I},
      sgn (w j) * sgn (z j) * (sgn (w l) * sgn (z l)) = 2 ^ Fintype.card {j // j ∉ I} := by
    intro j
    rw [sum_comm]
    have h2 : ∀ l : {j // j ∉ I}, ∑ w : {j // j ∉ I} → Bool,
        sgn (w j) * sgn (z j) * (sgn (w l) * sgn (z l))
        = sgn (z j) * sgn (z l) * ∑ w : {j // j ∉ I} → Bool, chi {j} w * chi {l} w := by
      intro l; rw [mul_sum]; refine sum_congr rfl (fun w _ => ?_); simp [chi]; ring
    rw [sum_congr rfl (fun l _ => h2 l)]
    simp_rw [sum_chi_mul_chi, Finset.singleton_inj, mul_ite, mul_zero]
    rw [sum_ite_eq]
    simp [← sq, sgn_sq]
  rw [sum_congr rfl (fun j _ => this j)]
  simp

/-- Lower bound on the atom probability. -/
theorem pAtom_ge (I : Finset (Fin n)) (z : Fin n → Bool) :
    (3 / 4) / (2 * (rad n : ℝ) + 1) ≤ pAtom (Tset n) I z := by
  classical
  set R : Type := {j // j ∉ I}
  set D : ℝ := (2 : ℝ) ^ Fintype.card R with hD
  have hDpos : 0 < D := by positivity
  have hr : (0 : ℝ) < rad n := by unfold rad; positivity
  -- Chebyshev: few w have |outside| ≥ rad
  set bad := univ.filter (fun w : R → Bool => (rad n : ℝ) ≤ |outside I z w|) with hbad
  have hcheb : (bad.card : ℝ) * (rad n : ℝ) ^ 2 ≤ (Fintype.card R : ℝ) * D := by
    rw [hD, ← sum_outside_sq I z]
    calc (bad.card : ℝ) * (rad n : ℝ) ^ 2 = ∑ w ∈ bad, (rad n : ℝ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ bad, outside I z w ^ 2 := by
          refine sum_le_sum (fun w hw => ?_)
          simp only [hbad, mem_filter, mem_univ, true_and] at hw
          calc (rad n : ℝ) ^ 2 ≤ |outside I z w| ^ 2 := pow_le_pow_left₀ hr.le hw 2
            _ = outside I z w ^ 2 := sq_abs _
      _ ≤ ∑ w, outside I z w ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ => sq_nonneg _)
  have hcardR : (Fintype.card R : ℝ) ≤ n := by
    have : Fintype.card R ≤ n := by
      calc Fintype.card R ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
        _ = n := Fintype.card_fin n
    exact_mod_cast this
  have hr2 : (4 : ℝ) * n ≤ (rad n : ℝ) ^ 2 := by
    have h1 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    have h2 : (n : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
      have : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) * ((Nat.sqrt n : ℝ) + 1) := by exact_mod_cast h1
      nlinarith
    unfold rad; push_cast; nlinarith
  have hbadle : (bad.card : ℝ) ≤ D / 4 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (bad.card : ℝ) * (4 * n) ≤ n * D := by
      calc (bad.card : ℝ) * (4 * n) ≤ (bad.card : ℝ) * (rad n : ℝ) ^ 2 := by gcongr
        _ ≤ (Fintype.card R : ℝ) * D := hcheb
        _ ≤ n * D := by gcongr
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- n = 0: then R is empty and outside = 0 < rad, so bad is empty
      have hR0 : Fintype.card R = 0 := by
        have : Fintype.card R ≤ n := by
          calc Fintype.card R ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
            _ = n := Fintype.card_fin n
        omega
      have hbad0 : bad = ∅ := by
        rw [hbad, filter_eq_empty_iff]
        intro w _
        have : outside I z w = 0 := by
          unfold outside
          rw [Fintype.card_eq_zero_iff] at hR0
          simp
        rw [this, abs_zero, not_le]; exact hr
      rw [hbad0]; simp; positivity
    · have hn : (0 : ℝ) < n := by exact_mod_cast hnpos
      rw [le_div_iff₀ (by norm_num)]
      by_contra hc
      push Not at hc
      nlinarith [mul_pos (sub_pos.mpr hc) hn]
  -- good w each contribute exactly one threshold
  set good := univ.filter (fun w : R → Bool => |outside I z w| < (rad n : ℝ)) with hgood
  have hgoodcard : 3 / 4 * D ≤ (good.card : ℝ) := by
    have hsplit : (good.card : ℝ) + bad.card = D := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (R → Bool)))
        (fun w : R → Bool => |outside I z w| < (rad n : ℝ))
      have hnot : univ.filter (fun w : R → Bool => ¬ |outside I z w| < (rad n : ℝ)) = bad := by
        rw [hbad]; congr 1; ext w; simp [not_lt]
      rw [hnot, card_univ, Fintype.card_fun, Fintype.card_bool] at this
      rw [hD]; exact_mod_cast this
    linarith
  -- the atom set contains a copy of `good`
  have hatom : (good.card : ℝ) ≤ ((univ.filter (fun θ : (R → Bool) × Tset n =>
      tau (Tset n) I z θ = 1)).card : ℝ) := by
    have hinj : ∀ w ∈ good, (1 + outsideZ I z w) ∈ Tset n := by
      intro w hw
      simp only [hgood, mem_filter, mem_univ, true_and, outside_eq] at hw
      have hw' : |(outsideZ I z w : ℝ)| < (rad n : ℝ) := hw
      rw [abs_lt] at hw'
      have h1 : -(rad n) < outsideZ I z w := by exact_mod_cast hw'.1
      have h2 : outsideZ I z w < rad n := by exact_mod_cast hw'.2
      simp only [Tset, mem_Icc]; constructor <;> omega
    let φ : good → (R → Bool) × Tset n := fun w => (w.1, ⟨1 + outsideZ I z w.1, hinj w.1 w.2⟩)
    have hφinj : Function.Injective φ := by
      intro a b hab; simp only [φ, Prod.mk.injEq] at hab; exact Subtype.ext hab.1
    have : good.card ≤ (univ.filter (fun θ : (R → Bool) × Tset n => tau (Tset n) I z θ = 1)).card := by
      rw [← Fintype.card_coe good]
      calc Fintype.card good ≤ Fintype.card
            (univ.filter (fun θ : (R → Bool) × Tset n => tau (Tset n) I z θ = 1)) := by
            refine Fintype.card_le_of_injective (fun w => ⟨φ w, ?_⟩) ?_
            · simp only [mem_filter, mem_univ, true_and, tau, φ, outside_eq]
              push_cast; ring
            · intro a b hab; exact hφinj (congrArg Subtype.val hab)
        _ = _ := Fintype.card_coe _
    exact_mod_cast this
  -- assemble
  unfold pAtom
  have hcardΘ : (Fintype.card ((R → Bool) × Tset n) : ℝ) = D * (2 * (rad n : ℝ) + 1) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    simp only [Tset, Int.card_Icc]
    rw [hD]
    have hx : (((rad n + 1 - -rad n).toNat : ℕ) : ℤ) = 2 * rad n + 1 := by
      have h0 : 0 ≤ rad n := by unfold rad; positivity
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have hx' : (((rad n + 1 - -rad n).toNat : ℕ) : ℝ) = 2 * (rad n : ℝ) + 1 := by
      exact_mod_cast hx
    push_cast
    rw [hx']
  rw [hcardΘ, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hgoodcard, hatom]

end

end ProblemQ
