import Mathlib

/-!
# Fourier analysis on the Boolean cube `ι → Bool`

`sgn true = 1`, `sgn false = -1`; characters `chi S x = ∏ i ∈ S, sgn (x i)`;
`fourier f S = 2^{-|ι|} ∑ₓ f x * chi S x`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

/-- `±1` encoding of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl
@[simp] lemma sgn_false : sgn false = -1 := rfl

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by rw [sq, sgn_mul_self]

lemma sgn_mul_sgn (a b : Bool) : sgn a * sgn b = sgn (a == b) := by
  cases a <;> cases b <;> simp [sgn]

lemma sum_sgn : ∑ b : Bool, sgn b = 0 := by simp [sgn]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Character of the cube. -/
def chi (S : Finset ι) (x : ι → Bool) : ℝ := ∏ i ∈ S, sgn (x i)

/-- Fourier coefficient. -/
def fourier (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  (∑ x, f x * chi S x) / (2 : ℝ) ^ Fintype.card ι

lemma chi_eq_prod_ite (S : Finset ι) (x : ι → Bool) :
    chi S x = ∏ i, (if i ∈ S then sgn (x i) else 1) := by
  unfold chi; rw [Finset.prod_ite_mem, univ_inter]

lemma chi_mul_chi (S T : Finset ι) (x : ι → Bool) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod_ite, chi_eq_prod_ite, chi_eq_prod_ite, ← prod_mul_distrib]
  refine prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, sgn_mul_self]

/-- Sum of a character over the cube. -/
lemma sum_chi (S : Finset ι) :
    ∑ x : ι → Bool, chi S x = if S = ∅ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp_rw [chi_eq_prod_ite]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if i ∈ S then sgn b else 1)]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
    apply prod_eq_zero (mem_univ i)
    simp [hi, sgn]

lemma sum_chi_mul_chi (S T : Finset ι) :
    ∑ x : ι → Bool, chi S x * chi T x
      = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp_rw [chi_mul_chi, sum_chi]
  congr 1
  simp

lemma chi_sq (S : Finset ι) (x : ι → Bool) : chi S x ^ 2 = 1 := by
  unfold chi; rw [← prod_pow]; exact prod_eq_one (fun i _ => sgn_sq _)

/-- Bessel's inequality for any family of distinct characters. -/
lemma bessel (f : (ι → Bool) → ℝ) (𝒮 : Finset (Finset ι)) :
    ∑ S ∈ 𝒮, fourier f S ^ 2 ≤ (∑ x, f x ^ 2) / (2 : ℝ) ^ Fintype.card ι := by
  set D : ℝ := (2 : ℝ) ^ Fintype.card ι with hD
  have hDpos : 0 < D := by positivity
  set a : Finset ι → ℝ := fun S => fourier f S with ha
  have hf : ∀ S, ∑ x, f x * chi S x = D * a S := by
    intro S; rw [ha, hD]; unfold fourier; field_simp
  have hcross : ∑ x, f x * ∑ S ∈ 𝒮, a S * chi S x = D * ∑ S ∈ 𝒮, a S ^ 2 := by
    calc ∑ x, f x * ∑ S ∈ 𝒮, a S * chi S x
        = ∑ S ∈ 𝒮, a S * ∑ x, f x * chi S x := by
          simp_rw [mul_sum]; rw [sum_comm]
          exact sum_congr rfl (fun S _ => sum_congr rfl (fun x _ => by ring))
      _ = ∑ S ∈ 𝒮, D * a S ^ 2 := sum_congr rfl (fun S _ => by rw [hf S]; ring)
      _ = D * ∑ S ∈ 𝒮, a S ^ 2 := by rw [mul_sum]
  have hsq : ∑ x, (∑ S ∈ 𝒮, a S * chi S x) ^ 2 = D * ∑ S ∈ 𝒮, a S ^ 2 := by
    calc ∑ x, (∑ S ∈ 𝒮, a S * chi S x) ^ 2
        = ∑ S ∈ 𝒮, ∑ T ∈ 𝒮, a S * a T * ∑ x, chi S x * chi T x := by
          simp_rw [sq, sum_mul_sum, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl (fun S _ => ?_)
          rw [sum_comm]
          exact sum_congr rfl (fun T _ => sum_congr rfl (fun x _ => by ring))
      _ = ∑ S ∈ 𝒮, D * a S ^ 2 := by
          refine sum_congr rfl (fun S hS => ?_)
          simp_rw [sum_chi_mul_chi, ← hD, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [hS]; ring
      _ = D * ∑ S ∈ 𝒮, a S ^ 2 := by rw [mul_sum]
  have hnonneg : 0 ≤ ∑ x, (f x - ∑ S ∈ 𝒮, a S * chi S x) ^ 2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  have expand : ∑ x, (f x - ∑ S ∈ 𝒮, a S * chi S x) ^ 2
      = ∑ x, f x ^ 2 - 2 * ∑ x, f x * ∑ S ∈ 𝒮, a S * chi S x
        + ∑ x, (∑ S ∈ 𝒮, a S * chi S x) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun x _ => by ring)
  rw [expand, hcross, hsq] at hnonneg
  rw [le_div_iff₀ hDpos]
  have : ∑ S ∈ 𝒮, fourier f S ^ 2 = ∑ S ∈ 𝒮, a S ^ 2 := rfl
  rw [this]
  linarith

end

end ProblemQ
