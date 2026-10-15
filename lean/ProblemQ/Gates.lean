import ProblemQ.Cube
import ProblemQ.Smoothing

/-!
# Fourier structure of random restricted threshold gates

On a column with live coordinates `ι`, a gate restricts to
`y ↦ 1[τ ≤ ∑ⱼ sgn(w j) sgn(y j)]`. With `w` uniform and independent of `τ`, the level-3
Fourier vector has a diagonal covariance bounded below by `Pr[τ = 1] · F̂₁(S)²`.
-/

open Finset BigOperators
open scoped RealInnerProductSpace

namespace ProblemQ

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restricted gate as a function on the live cube. -/
def gateFun (w : ι → Bool) (τ : ℝ) (y : ι → Bool) : ℝ :=
  if τ ≤ ∑ j, sgn (w j) * sgn (y j) then 1 else 0

/-- Untwisted threshold function `y ↦ 1[τ ≤ ∑ sgn y]`. -/
def thrFun (τ : ℝ) (y : ι → Bool) : ℝ :=
  if τ ≤ ∑ j, sgn (y j) then 1 else 0

/-- The twist `x ↦ (w == x)` is an involution of the cube. -/
def twist (w : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x j := w j == x j
  invFun x j := w j == x j
  left_inv x := by
    funext j; show (w j == (w j == x j)) = x j; cases w j <;> cases x j <;> rfl
  right_inv x := by
    funext j; show (w j == (w j == x j)) = x j; cases w j <;> cases x j <;> rfl

lemma chi_twist (S : Finset ι) (w x : ι → Bool) :
    chi S (twist w x) = chi S w * chi S x := by
  unfold chi; rw [← prod_mul_distrib]
  refine prod_congr rfl (fun j _ => ?_)
  rw [sgn_mul_sgn]; rfl

lemma fourier_gateFun (w : ι → Bool) (τ : ℝ) (S : Finset ι) :
    fourier (gateFun w τ) S = chi S w * fourier (thrFun τ) S := by
  unfold fourier
  rw [mul_div_assoc', mul_sum]
  congr 1
  rw [← Equiv.sum_comp (twist w)]
  refine sum_congr rfl (fun x _ => ?_)
  have h : ∑ j, sgn (w j) * sgn (twist w x j) = ∑ j, sgn (x j) := by
    refine sum_congr rfl (fun j _ => ?_)
    show sgn (w j) * sgn (w j == x j) = sgn (x j)
    cases w j <;> cases x j <;> simp [sgn]
  simp only [gateFun, thrFun, h, chi_twist]
  ring

/-- Index type of level-3 characters. -/
abbrev L3 (ι : Type*) [Fintype ι] [DecidableEq ι] := {S : Finset ι // S.card = 3}

/-- Level-3 Fourier vector of a function. -/
def lvl3 (f : (ι → Bool) → ℝ) : EuclideanSpace ℝ (L3 ι) :=
  WithLp.toLp 2 (fun S => fourier f S.1)

lemma lvl3_apply (f : (ι → Bool) → ℝ) (S : L3 ι) : lvl3 f S = fourier f S.1 := rfl

lemma fourier_sub (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourier (fun y => f y - g y) S = fourier f S - fourier g S := by
  unfold fourier; rw [← sub_div]; congr 1; rw [← sum_sub_distrib]
  exact sum_congr rfl (fun x _ => by ring)

/-- Bessel on the level-3 vector. -/
lemma norm_lvl3_sq_le (f : (ι → Bool) → ℝ) :
    ‖lvl3 f‖ ^ 2 ≤ (∑ x, f x ^ 2) / (2 : ℝ) ^ Fintype.card ι := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [lvl3_apply, Real.norm_eq_abs, sq_abs]
  have := bessel f (univ.filter (fun S : Finset ι => S.card = 3))
  refine le_trans (le_of_eq ?_) this
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]

lemma inner_lvl3 (v : EuclideanSpace ℝ (L3 ι)) (f : (ι → Bool) → ℝ) :
    ⟪v, lvl3 f⟫ = ∑ S : L3 ι, v S * fourier f S.1 := by
  rw [PiLp.inner_apply]
  refine sum_congr rfl (fun S _ => ?_)
  simp [lvl3_apply, mul_comm]

lemma sum_pair_sq {α : Type*} [Fintype α] (a : α → ℝ) :
    ∑ x, ∑ y, (a x - a y) ^ 2
      = 2 * (Fintype.card α : ℝ) * ∑ x, a x ^ 2 - 2 * (∑ x, a x) ^ 2 := by
  have : ∀ x y, (a x - a y) ^ 2 = a x ^ 2 + a y ^ 2 - 2 * (a x * a y) := fun x y => by ring
  simp_rw [this, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
    ← sum_mul, sq (∑ x, a x)]
  rw [sum_mul_sum]
  ring

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]

/-- Level-3 vector of the restricted gate indexed by `(w, θ)`. -/
def gateVec (τ : Θ → ℝ) (γ : (ι → Bool) × Θ) : EuclideanSpace ℝ (L3 ι) :=
  lvl3 (gateFun γ.1 (τ γ.2))

/-- **Covariance lower bound** (pair form) for random restricted gates. -/
theorem gateVec_var (τ : Θ → ℝ) {f : ℝ} (hf0 : 0 ≤ f)
    (hf : ∀ S : L3 ι, f ≤ fourier (thrFun 1) S.1 ^ 2) (v : EuclideanSpace ℝ (L3 ι)) :
    2 * (((univ.filter (fun θ => τ θ = 1)).card : ℝ) / Fintype.card Θ * f) * ‖v‖ ^ 2 ≤
      (∑ γ, ∑ γ', ⟪v, gateVec τ γ - gateVec τ γ'⟫ ^ 2)
        / (Fintype.card ((ι → Bool) × Θ) : ℝ) ^ 2 := by
  set D : ℝ := (2 : ℝ) ^ Fintype.card ι with hD
  have hDpos : 0 < D := by positivity
  have hTpos : (0 : ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card ((ι → Bool) × Θ) : ℝ) = D * Fintype.card Θ := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hD]; push_cast; ring
  set F : Θ → L3 ι → ℝ := fun θ S => fourier (thrFun (τ θ)) S.1 with hF
  set a : (ι → Bool) × Θ → ℝ := fun γ => ⟪v, gateVec τ γ⟫ with ha
  have ha' : ∀ w θ, a (w, θ) = ∑ S : L3 ι, v S * chi S.1 w * F θ S := by
    intro w θ
    simp only [ha, gateVec, inner_lvl3, fourier_gateFun, hF]
    exact sum_congr rfl (fun S _ => by ring)
  have hsub : ∀ γ γ', ⟪v, gateVec τ γ - gateVec τ γ'⟫ = a γ - a γ' := by
    intro γ γ'; rw [inner_sub_right]
  simp_rw [hsub]
  rw [sum_pair_sq]
  -- the mean vanishes
  have ha'' : ∀ γ : (ι → Bool) × Θ, a γ = ∑ S : L3 ι, v S * chi S.1 γ.1 * F γ.2 S :=
    fun γ => ha' γ.1 γ.2
  have hmean : ∑ γ, a γ = 0 := by
    simp_rw [ha'']
    rw [sum_comm]
    apply sum_eq_zero
    intro S _
    rw [Fintype.sum_prod_type]
    have hS : S.1 ≠ ∅ := by
      intro h; have := S.2; rw [h] at this; simp at this
    have : ∑ w : ι → Bool, ∑ θ : Θ, v S * chi S.1 (w, θ).1 * F (w, θ).2 S
        = v S * ((∑ w : ι → Bool, chi S.1 w) * ∑ θ, F θ S) := by
      rw [sum_mul_sum, mul_sum]
      refine sum_congr rfl (fun w _ => ?_)
      rw [mul_sum]
      exact sum_congr rfl (fun θ _ => by simp only; ring)
    rw [this, sum_chi, if_neg hS]
    simp
  -- the second moment
  have hsecond : ∑ γ, a γ ^ 2 = D * ∑ θ, ∑ S : L3 ι, v S ^ 2 * F θ S ^ 2 := by
    rw [Fintype.sum_prod_type, sum_comm, mul_sum]
    refine sum_congr rfl (fun θ _ => ?_)
    simp_rw [ha', sq, sum_mul_sum]
    rw [sum_comm]
    have : ∀ S : L3 ι, ∑ w : ι → Bool, ∑ T : L3 ι,
        v S * chi S.1 w * F θ S * (v T * chi T.1 w * F θ T) = D * (v S * F θ S * (v S * F θ S)) := by
      intro S
      rw [sum_comm]
      have : ∀ T : L3 ι, ∑ w : ι → Bool, v S * chi S.1 w * F θ S * (v T * chi T.1 w * F θ T)
          = v S * F θ S * (v T * F θ T) * ∑ w, chi S.1 w * chi T.1 w := by
        intro T; rw [mul_sum]; exact sum_congr rfl (fun w _ => by ring)
      rw [sum_congr rfl (fun T _ => this T)]
      simp_rw [sum_chi_mul_chi, ← hD, Subtype.ext_iff.symm]
      simp [mul_ite]
      ring
    rw [sum_congr rfl (fun S _ => this S), ← mul_sum]
    congr 1
    exact sum_congr rfl (fun S _ => by ring)
  -- lower bound on the second moment
  have hlow : ((univ.filter (fun θ => τ θ = 1)).card : ℝ) * f * ‖v‖ ^ 2
      ≤ ∑ θ, ∑ S : L3 ι, v S ^ 2 * F θ S ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← sum_filter_add_sum_filter_not univ (fun θ => τ θ = 1)]
    have h1 : ∀ θ ∈ univ.filter (fun θ => τ θ = 1),
        f * ∑ S : L3 ι, v S ^ 2 ≤ ∑ S : L3 ι, v S ^ 2 * F θ S ^ 2 := by
      intro θ hθ
      simp only [mem_filter, mem_univ, true_and] at hθ
      rw [mul_sum]
      refine sum_le_sum (fun S _ => ?_)
      have : F θ S = fourier (thrFun 1) S.1 := by simp [hF, hθ]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left (hf S) (sq_nonneg _)
    have h2 : 0 ≤ ∑ θ ∈ univ.filter (fun θ => ¬ τ θ = 1), ∑ S : L3 ι, v S ^ 2 * F θ S ^ 2 :=
      sum_nonneg (fun θ _ => sum_nonneg (fun S _ => by positivity))
    have h3 := sum_le_sum h1
    rw [sum_const, nsmul_eq_mul] at h3
    nlinarith
  rw [hmean, hcard, hsecond]
  rw [le_div_iff₀ (by positivity)]
  have hT := hTpos
  have key : 2 * ((univ.filter (fun θ => τ θ = 1)).card / (Fintype.card Θ : ℝ) * f) * ‖v‖ ^ 2
        * (D * Fintype.card Θ) ^ 2
      = 2 * (D * Fintype.card Θ) * D * (((univ.filter (fun θ => τ θ = 1)).card : ℝ) * f * ‖v‖ ^ 2) := by
    field_simp
  rw [key]
  have : 0 ≤ 2 * (D * Fintype.card Θ) * D := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlow this]

end

end ProblemQ
