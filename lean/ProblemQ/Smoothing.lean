import Mathlib

/-!
# Smoothing small-ball bound for sums of independent bounded vectors

Finite uniform probability space `Γ`, vectors `X : Γ → E` (`E = EuclideanSpace ℝ ι`, `N = card ι`),
coefficients `α i ∈ {1, -1, 0}`. For `ω : Fin m → Γ` put `V ω = ∑ i, α i • X (ω i)`.
If `X` has variance at least `s` in every direction (pair form) and diameter at most `M`,
the fraction of `ω` with `‖V ω - c‖ ≤ R` is at most
`exp(N/2) * ((b/(b+a))^(N/2) + 2^(N/2) * exp(-b/(2M²)))`, `b = R²/(2N)`, `a = (43/96) m' s`.
-/

open Finset BigOperators MeasureTheory Complex
open scoped RealInnerProductSpace

namespace ProblemQ

noncomputable section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-- Real Gaussian integrability on `E`. -/
lemma integrable_rexp_neg_mul_sq_norm' {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : E => Real.exp (-b * ‖v‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall (fun v => ?_))
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← ofReal_pow]

lemma integral_rexp_neg_mul_sq_norm' {b : ℝ} (hb : 0 < b) :
    ∫ v : E, Real.exp (-b * ‖v‖ ^ 2) = (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace]

/-- Gaussian representation: `∫ exp(-b‖v‖² + i⟪u,v⟫) dv = (π/b)^(N/2) exp(-‖u‖²/(4b))`. -/
lemma gauss_repr {b : ℝ} (hb : 0 < b) (u : E) :
    ∫ v : E, cexp (-(b : ℂ) * ‖v‖ ^ 2 + I * ⟪u, v⟫)
      = ((Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-‖u‖ ^ 2 / (4 * b)) : ℝ) := by
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb),
    finrank_euclideanSpace]
  rw [ofReal_mul, ofReal_exp]
  congr 1
  · rw [← ofReal_div, ofReal_cpow (by positivity)]
    push_cast; ring_nf
  · congr 1
    rw [I_sq]; push_cast; ring

/-- Characteristic function of the uniform distribution of `X`. -/
def charF {Γ : Type*} [Fintype Γ] (X : Γ → E) (v : E) : ℂ :=
  (∑ γ, cexp (I * ⟪X γ, v⟫)) / (Fintype.card Γ : ℂ)

variable {Γ : Type*} [Fintype Γ] [Nonempty Γ]

lemma card_pos' : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos

/-- `‖∑ e^{iθ}‖² = ∑∑ cos(θ - θ')`. -/
lemma norm_sum_cexp_sq (θ : Γ → ℝ) :
    ‖∑ γ, cexp (I * θ γ)‖ ^ 2 = ∑ γ, ∑ γ', Real.cos (θ γ - θ γ') := by
  have hre : (∑ γ, cexp (I * θ γ)).re = ∑ γ, Real.cos (θ γ) := by
    rw [re_sum]; refine sum_congr rfl (fun γ _ => ?_)
    rw [mul_comm, exp_ofReal_mul_I_re]
  have him : (∑ γ, cexp (I * θ γ)).im = ∑ γ, Real.sin (θ γ) := by
    rw [im_sum]; refine sum_congr rfl (fun γ _ => ?_)
    rw [mul_comm, exp_ofReal_mul_I_im]
  rw [← normSq_eq_norm_sq, normSq_apply, hre, him]
  simp_rw [sum_mul_sum, ← sum_add_distrib, Real.cos_sub]

lemma cos_le_quad {x : ℝ} (hx : |x| ≤ 1) : Real.cos x ≤ 1 - (43 / 96) * x ^ 2 := by
  have h := Real.cos_bound hx
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have : |x| ^ 4 = |x| ^ 2 * |x| ^ 2 := by ring
    rw [this, sq_abs]
    have : x ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg x]
    nlinarith [sq_nonneg x]
  have := (abs_le.mp h).2
  nlinarith

/-- Decay of the characteristic function near the origin. -/
lemma charF_le (X : Γ → E) {s M : ℝ} (hM : 0 < M)
    (hvar : ∀ v : E, 2 * s * ‖v‖ ^ 2 ≤
      (∑ γ, ∑ γ', ⟪v, X γ - X γ'⟫ ^ 2) / (Fintype.card Γ : ℝ) ^ 2)
    (hdiam : ∀ γ γ', ‖X γ - X γ'‖ ≤ M) (v : E) (hv : M * ‖v‖ ≤ 1) :
    ‖charF X v‖ ≤ Real.exp (-(43 / 96) * s * ‖v‖ ^ 2) := by
  set C : ℝ := (Fintype.card Γ : ℝ) with hC
  have hCpos : 0 < C := card_pos'
  have hsq : ‖charF X v‖ ^ 2
      = (∑ γ, ∑ γ', Real.cos (⟪X γ, v⟫ - ⟪X γ', v⟫)) / C ^ 2 := by
    unfold charF
    rw [norm_div, div_pow, norm_sum_cexp_sq (fun γ => ⟪X γ, v⟫)]
    congr 1
    rw [hC]; simp
  have hcos : ∀ γ γ', Real.cos (⟪X γ, v⟫ - ⟪X γ', v⟫)
      ≤ 1 - (43 / 96) * ⟪v, X γ - X γ'⟫ ^ 2 := by
    intro γ γ'
    have heq : ⟪X γ, v⟫ - ⟪X γ', v⟫ = ⟪v, X γ - X γ'⟫ := by
      rw [inner_sub_right, real_inner_comm v (X γ), real_inner_comm v (X γ')]
    rw [heq]
    apply cos_le_quad
    calc |⟪v, X γ - X γ'⟫| ≤ ‖v‖ * ‖X γ - X γ'‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * M := by gcongr; exact hdiam γ γ'
      _ = M * ‖v‖ := by ring
      _ ≤ 1 := hv
  have hle : ‖charF X v‖ ^ 2 ≤ 1 - (43 / 48) * s * ‖v‖ ^ 2 := by
    rw [hsq, div_le_iff₀ (by positivity)]
    have h1 : ∑ γ, ∑ γ', Real.cos (⟪X γ, v⟫ - ⟪X γ', v⟫)
        ≤ ∑ γ : Γ, ∑ γ' : Γ, (1 - (43 / 96) * ⟪v, X γ - X γ'⟫ ^ 2) :=
      sum_le_sum (fun γ _ => sum_le_sum (fun γ' _ => hcos γ γ'))
    have h2 : ∑ γ : Γ, ∑ γ' : Γ, (1 - (43 / 96) * ⟪v, X γ - X γ'⟫ ^ 2)
        = C ^ 2 - (43 / 96) * ∑ γ, ∑ γ', ⟪v, X γ - X γ'⟫ ^ 2 := by
      simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_sum]
      rw [hC]; ring
    have h3 := hvar v
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith
  have hexp : 1 - (43 / 48) * s * ‖v‖ ^ 2 ≤ Real.exp (-(43 / 48) * s * ‖v‖ ^ 2) := by
    have := Real.add_one_le_exp (-(43 / 48) * s * ‖v‖ ^ 2); linarith
  have hfin : ‖charF X v‖ ^ 2 ≤ (Real.exp (-(43 / 96) * s * ‖v‖ ^ 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast
    calc ‖charF X v‖ ^ 2 ≤ Real.exp (-(43 / 48) * s * ‖v‖ ^ 2) := hle.trans hexp
      _ = Real.exp (2 * (-(43 / 96) * s * ‖v‖ ^ 2)) := by ring_nf
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp hfin

lemma charF_norm_le_one (X : Γ → E) (v : E) : ‖charF X v‖ ≤ 1 := by
  unfold charF
  rw [norm_div]
  rw [div_le_one (by simpa using (card_pos' (Γ := Γ)))]
  calc ‖∑ γ, cexp (I * ⟪X γ, v⟫)‖ ≤ ∑ γ : Γ, ‖cexp (I * ⟪X γ, v⟫)‖ := norm_sum_le _ _
    _ = ∑ γ : Γ, (1 : ℝ) := by
        refine sum_congr rfl (fun γ _ => ?_)
        rw [mul_comm]; exact norm_exp_ofReal_mul_I _
    _ = ‖(Fintype.card Γ : ℂ)‖ := by simp

lemma charF_zero (X : Γ → E) : charF X 0 = 1 := by
  unfold charF
  simp only [inner_zero_right, ofReal_zero, mul_zero, Complex.exp_zero, sum_const, card_univ,
    nsmul_eq_mul, mul_one]
  exact div_self (by simpa using (Fintype.card_pos (α := Γ)).ne')

lemma sum_charF_eq (X : Γ → E) (v : E) :
    ∑ γ, cexp (I * ⟪X γ, v⟫) = (Fintype.card Γ : ℂ) * charF X v := by
  unfold charF
  have : (Fintype.card Γ : ℂ) ≠ 0 := by simpa using (Fintype.card_pos (α := Γ)).ne'
  field_simp

/-- Factorisation of the characteristic function of the independent sum. -/
lemma sum_omega_cexp {m : ℕ} (X : Γ → E) (α : Fin m → ℝ) (c v : E) :
    ∑ ω : Fin m → Γ, cexp (I * ⟪(∑ i, α i • X (ω i)) - c, v⟫)
      = cexp (-(I * ⟪c, v⟫)) * ∏ i, ((Fintype.card Γ : ℂ) * charF X (α i • v)) := by
  have h1 : ∀ ω : Fin m → Γ, cexp (I * ⟪(∑ i, α i • X (ω i)) - c, v⟫)
      = cexp (-(I * ⟪c, v⟫)) * ∏ i, cexp (I * ⟪X (ω i), α i • v⟫) := by
    intro ω
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [inner_sub_left, sum_inner]
    simp only [real_inner_smul_left, real_inner_smul_right, ofReal_sub, ofReal_sum, ofReal_mul,
      mul_sub, mul_sum]
    ring
  simp_rw [h1, ← mul_sum, ← sum_charF_eq]
  congr 1
  exact (Fintype.prod_sum (fun i γ => cexp (I * ⟪X γ, α i • v⟫))).symm

/-- Product of characteristic functions: `≤ exp(-a‖v‖²)` near `0`, `≤ 1` always. -/
lemma prod_charF_le {m : ℕ} (X : Γ → E) (α : Fin m → ℝ)
    (hα : ∀ i, α i = 1 ∨ α i = -1 ∨ α i = 0) {s M : ℝ} (hM : 0 < M)
    (hvar : ∀ v : E, 2 * s * ‖v‖ ^ 2 ≤
      (∑ γ, ∑ γ', ⟪v, X γ - X γ'⟫ ^ 2) / (Fintype.card Γ : ℝ) ^ 2)
    (hdiam : ∀ γ γ', ‖X γ - X γ'‖ ≤ M) (v : E) :
    ∏ i, ‖charF X (α i • v)‖ ≤ 1 ∧
    (M * ‖v‖ ≤ 1 → ∏ i, ‖charF X (α i • v)‖
      ≤ Real.exp (-((43 / 96) * s * ((univ.filter (fun i => α i ≠ 0)).card : ℝ)) * ‖v‖ ^ 2)) := by
  constructor
  · exact prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => charF_norm_le_one X _)
  · intro hv
    have hfac : ∀ i, ‖charF X (α i • v)‖
        ≤ if α i ≠ 0 then Real.exp (-(43 / 96) * s * ‖v‖ ^ 2) else 1 := by
      intro i
      rcases hα i with h | h | h
      · simp only [h, ne_eq, one_ne_zero, not_false_eq_true, ite_true, one_smul]
        exact charF_le X hM hvar hdiam v hv
      · simp only [h, ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true, ite_true, neg_smul,
          one_smul]
        have := charF_le X hM hvar hdiam (-v) (by rwa [norm_neg])
        rwa [norm_neg] at this
      · simp [h, charF_zero]
    calc ∏ i, ‖charF X (α i • v)‖
        ≤ ∏ i, (if α i ≠ 0 then Real.exp (-(43 / 96) * s * ‖v‖ ^ 2) else 1) :=
          prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hfac i)
      _ = Real.exp (-(43 / 96) * s * ‖v‖ ^ 2) ^ (univ.filter (fun i => α i ≠ 0)).card := by
          rw [prod_ite, prod_const_one, mul_one, prod_const]
      _ = _ := by
          rw [← Real.exp_nat_mul]; congr 1; ring

/-- **Smoothing small-ball bound.** -/
theorem small_ball {m : ℕ} (hN : 0 < Fintype.card ι) (X : Γ → E) (α : Fin m → ℝ)
    (hα : ∀ i, α i = 1 ∨ α i = -1 ∨ α i = 0) {s M R : ℝ} (hs : 0 ≤ s) (hM : 0 < M)
    (hR : 0 < R)
    (hvar : ∀ v : E, 2 * s * ‖v‖ ^ 2 ≤
      (∑ γ, ∑ γ', ⟪v, X γ - X γ'⟫ ^ 2) / (Fintype.card Γ : ℝ) ^ 2)
    (hdiam : ∀ γ γ', ‖X γ - X γ'‖ ≤ M) (c : E) :
    ((univ.filter (fun ω : Fin m → Γ => ‖(∑ i, α i • X (ω i)) - c‖ ≤ R)).card : ℝ)
      / (Fintype.card Γ : ℝ) ^ m
    ≤ Real.exp ((Fintype.card ι : ℝ) / 2) *
      ((R ^ 2 / (2 * (Fintype.card ι : ℝ)) / (R ^ 2 / (2 * (Fintype.card ι : ℝ)) +
          (43 / 96) * s * ((univ.filter (fun i => α i ≠ 0)).card : ℝ))) ^ ((Fintype.card ι : ℝ) / 2)
        + 2 ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-(R ^ 2 / (2 * (Fintype.card ι : ℝ))) / (2 * M ^ 2))) := by
  set C : ℝ := (Fintype.card Γ : ℝ) with hC
  have hCpos : 0 < C := card_pos'
  set b : ℝ := R ^ 2 / (2 * (Fintype.card ι : ℝ)) with hb
  have hbpos : 0 < b := by positivity
  set a : ℝ := (43 / 96) * s * ((univ.filter (fun i => α i ≠ 0)).card : ℝ) with ha
  have hapos : 0 ≤ a := by positivity
  set u : (Fin m → Γ) → E := fun ω => (∑ i, α i • X (ω i)) - c with hu
  -- Step 1: indicator ≤ e^{N/2} e^{-‖u‖²/(4b)}
  have hind : ((univ.filter (fun ω : Fin m → Γ => ‖u ω‖ ≤ R)).card : ℝ)
      ≤ Real.exp ((Fintype.card ι : ℝ) / 2) * ∑ ω, Real.exp (-‖u ω‖ ^ 2 / (4 * b)) := by
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
    refine sum_le_sum (fun ω _ => ?_)
    split_ifs with h
    · rw [Nat.cast_one, ← Real.exp_add]
      apply Real.one_le_exp
      have h2 : ‖u ω‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      have : ‖u ω‖ ^ 2 / (4 * b) ≤ (Fintype.card ι : ℝ) / 2 := by
        rw [div_le_iff₀ (by positivity), hb]
        have hNpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
        field_simp
        nlinarith
      linarith [neg_div (4 * b) (‖u ω‖ ^ 2)]
    · positivity
  -- Step 2: Gaussian representation and exchange of sum and integral
  set F : E → ℂ := fun v => ∑ ω, cexp (-(b : ℂ) * ‖v‖ ^ 2 + I * ⟪u ω, v⟫) with hF
  have hrepr : ((Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) * ∑ ω, Real.exp (-‖u ω‖ ^ 2 / (4 * b)) : ℝ)
      = (∫ v, F v).re := by
    rw [hF, integral_finsetSum _ (fun ω _ =>
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using hbpos) I (u ω))]
    simp_rw [gauss_repr hbpos]
    rw [re_sum, mul_sum]
    simp only [ofReal_re]
  -- Step 3: pointwise bound of ‖F v‖
  set G : E → ℝ := fun v => Real.exp (-(b + a) * ‖v‖ ^ 2)
      + Real.exp (-b / (2 * M ^ 2)) * Real.exp (-(b / 2) * ‖v‖ ^ 2) with hG
  have hFle : ∀ v, ‖F v‖ ≤ C ^ m * G v := by
    intro v
    have hFv : F v = cexp (-(b : ℂ) * ‖v‖ ^ 2) *
        ∑ ω : Fin m → Γ, cexp (I * ⟪(∑ i, α i • X (ω i)) - c, v⟫) := by
      rw [hF, mul_sum]
      refine sum_congr rfl (fun ω _ => ?_)
      rw [← Complex.exp_add]
    rw [hFv, sum_omega_cexp, norm_mul, norm_mul, prod_mul_distrib, norm_mul, norm_prod,
      norm_prod]
    have hnorm1 : ‖cexp (-(I * ⟪c, v⟫))‖ = 1 := by
      rw [show -(I * (⟪c, v⟫ : ℂ)) = ((-⟪c, v⟫ : ℝ) : ℂ) * I by push_cast; ring]
      exact norm_exp_ofReal_mul_I _
    have hnormG : ‖cexp (-(b : ℂ) * ‖v‖ ^ 2)‖ = Real.exp (-b * ‖v‖ ^ 2) := by
      rw [Complex.norm_exp]; congr 1; simp [← ofReal_pow]
    have hnormC : ∏ i : Fin m, ‖(Fintype.card Γ : ℂ)‖ = C ^ m := by
      rw [prod_const, card_univ, Fintype.card_fin]; simp [hC]
    rw [hnorm1, hnormG, hnormC, one_mul]
    obtain ⟨hle1, hlenear⟩ := prod_charF_le X α hα hM hvar hdiam v
    have hP0 : 0 ≤ ∏ i, ‖charF X (α i • v)‖ := prod_nonneg (fun i _ => norm_nonneg _)
    suffices key : Real.exp (-b * ‖v‖ ^ 2) * ∏ i, ‖charF X (α i • v)‖ ≤ G v by
      calc Real.exp (-b * ‖v‖ ^ 2) * (C ^ m * ∏ i, ‖charF X (α i • v)‖)
          = C ^ m * (Real.exp (-b * ‖v‖ ^ 2) * ∏ i, ‖charF X (α i • v)‖) := by ring
        _ ≤ C ^ m * G v := by gcongr
    by_cases hv : M * ‖v‖ ≤ 1
    · have := hlenear hv
      calc Real.exp (-b * ‖v‖ ^ 2) * ∏ i, ‖charF X (α i • v)‖
          ≤ Real.exp (-b * ‖v‖ ^ 2) * Real.exp (-a * ‖v‖ ^ 2) := by
            gcongr
        _ = Real.exp (-(b + a) * ‖v‖ ^ 2) := by rw [← Real.exp_add]; ring_nf
        _ ≤ G v := by
            have := mul_nonneg (Real.exp_pos (-b / (2 * M ^ 2))).le
              (Real.exp_pos (-(b / 2) * ‖v‖ ^ 2)).le
            rw [hG]; linarith
    · push Not at hv
      have hv2 : 1 / M ^ 2 ≤ ‖v‖ ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
      calc Real.exp (-b * ‖v‖ ^ 2) * ∏ i, ‖charF X (α i • v)‖
          ≤ Real.exp (-b * ‖v‖ ^ 2) * 1 := by gcongr
        _ = Real.exp (-(b / 2) * ‖v‖ ^ 2 + -(b / 2) * ‖v‖ ^ 2) := by rw [mul_one]; ring_nf
        _ ≤ Real.exp (-b / (2 * M ^ 2) + -(b / 2) * ‖v‖ ^ 2) := by
            gcongr
            have : b / (2 * M ^ 2) = (b / 2) * (1 / M ^ 2) := by field_simp
            rw [neg_div, this]
            nlinarith
        _ = Real.exp (-b / (2 * M ^ 2)) * Real.exp (-(b / 2) * ‖v‖ ^ 2) := Real.exp_add _ _
        _ ≤ G v := by
            have := (Real.exp_pos (-(b + a) * ‖v‖ ^ 2)).le
            rw [hG]; linarith
  -- Step 4: integrate
  have hGint : Integrable G := by
    rw [hG]
    exact (integrable_rexp_neg_mul_sq_norm' (by positivity : 0 < b + a)).add
      ((integrable_rexp_neg_mul_sq_norm' (by positivity : 0 < b / 2)).const_mul _)
  have hGval : ∫ v, G v = (Real.pi / (b + a)) ^ ((Fintype.card ι : ℝ) / 2)
      + Real.exp (-b / (2 * M ^ 2)) * (Real.pi / (b / 2)) ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [hG, integral_add (integrable_rexp_neg_mul_sq_norm' (by positivity))
      ((integrable_rexp_neg_mul_sq_norm' (by positivity)).const_mul _), integral_const_mul,
      integral_rexp_neg_mul_sq_norm' (by positivity),
      integral_rexp_neg_mul_sq_norm' (by positivity)]
  have hmain : (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) * ∑ ω, Real.exp (-‖u ω‖ ^ 2 / (4 * b))
      ≤ C ^ m * ((Real.pi / (b + a)) ^ ((Fintype.card ι : ℝ) / 2)
        + Real.exp (-b / (2 * M ^ 2)) * (Real.pi / (b / 2)) ^ ((Fintype.card ι : ℝ) / 2)) := by
    rw [hrepr, ← hGval, ← integral_const_mul]
    calc (∫ v, F v).re ≤ ‖∫ v, F v‖ := re_le_norm _
      _ ≤ ∫ v, ‖F v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v, C ^ m * G v := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => norm_nonneg _))
            (hGint.const_mul _) (Filter.Eventually.of_forall hFle)
  -- Step 5: algebra
  have hpb : 0 < (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) := by positivity
  have hsum : ∑ ω, Real.exp (-‖u ω‖ ^ 2 / (4 * b))
      ≤ C ^ m * ((b / (b + a)) ^ ((Fintype.card ι : ℝ) / 2)
        + 2 ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-b / (2 * M ^ 2))) := by
    rw [← le_div_iff₀' hpb] at hmain
    refine hmain.trans (le_of_eq ?_)
    have e1 : (Real.pi / (b + a)) ^ ((Fintype.card ι : ℝ) / 2) / (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2)
        = (b / (b + a)) ^ ((Fintype.card ι : ℝ) / 2) := by
      rw [← Real.div_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    have e2 : (Real.pi / (b / 2)) ^ ((Fintype.card ι : ℝ) / 2) / (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2)
        = 2 ^ ((Fintype.card ι : ℝ) / 2) := by
      rw [← Real.div_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    rw [mul_div_assoc, add_div, mul_div_assoc, e1, e2]
    ring
  rw [div_le_iff₀ (by positivity)]
  calc ((univ.filter (fun ω : Fin m → Γ => ‖u ω‖ ≤ R)).card : ℝ)
      ≤ Real.exp ((Fintype.card ι : ℝ) / 2) * ∑ ω, Real.exp (-‖u ω‖ ^ 2 / (4 * b)) := hind
    _ ≤ Real.exp ((Fintype.card ι : ℝ) / 2) * (C ^ m * ((b / (b + a)) ^ ((Fintype.card ι : ℝ) / 2)
        + 2 ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-b / (2 * M ^ 2)))) := by gcongr
    _ = _ := by ring

end

end ProblemQ
