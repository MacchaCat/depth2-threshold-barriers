import Mathlib

/-!
# Bottom fan-in below `n` cannot compute parity

The restricted class "THR∘THR with bottom fan-in `s < n`" is trivial for lower bounds, at
**every** size: a bottom gate of fan-in `< n` ignores some coordinate, hence is orthogonal to the
parity character, so the top gate's linear form `H = ∑ αᵢ gᵢ - T` satisfies `∑ₓ H(x)·χ(x) = 0`.
If the circuit computed parity, every term `H(x)·χ(x)` would be `≤ 0` and the term at `x = 0`
would be `< 0`: contradiction. (This is Minsky–Papert's PTF-degree bound for parity, specialized.)

The bottom gates here are arbitrary Boolean functions that each ignore one coordinate; threshold
gates of fan-in `< n` are a special case. The top weights and threshold are arbitrary reals and
the number of gates `m` is arbitrary.
-/

open Finset

namespace ProblemQ

namespace FaninParity

variable {n : ℕ}

/-- Flip coordinate `j`. -/
def flipAt (j : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x j (!x j)

lemma flipAt_flipAt (j : Fin n) (x : Fin n → Bool) : flipAt j (flipAt j x) = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

/-- Flipping a coordinate, as an equivalence of the cube. -/
def flipEquiv (j : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  ⟨flipAt j, flipAt j, flipAt_flipAt j, flipAt_flipAt j⟩

/-- `g` does not read coordinate `j`. -/
def Ignores {β : Type*} (g : (Fin n → Bool) → β) (j : Fin n) : Prop :=
  ∀ x, g (flipAt j x) = g x

/-- The `±1` sign of a bit. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The parity character `χ(x) = ∏ᵢ (-1)^{xᵢ}`. -/
def chi (x : Fin n → Bool) : ℝ := ∏ i, sgn (x i)

/-- Number of ones. -/
def ones (x : Fin n → Bool) : ℕ := #(univ.filter (fun i => x i = true))

/-- Parity of `x`. -/
def parity (x : Fin n → Bool) : Bool := decide (ones x % 2 = 1)

lemma chi_flip (j : Fin n) (x : Fin n → Bool) : chi (flipAt j x) = - chi x := by
  unfold chi
  rw [← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ _ (mem_univ j)]
  have hrest : ∏ i ∈ univ.erase j, sgn (flipAt j x i) = ∏ i ∈ univ.erase j, sgn (x i) := by
    refine prod_congr rfl (fun i hi => ?_)
    rw [flipAt, Function.update_of_ne (ne_of_mem_erase hi)]
  rw [hrest]
  have hj : sgn (flipAt j x j) = - sgn (x j) := by
    simp only [flipAt, Function.update_self]
    cases x j <;> simp [sgn]
  rw [hj, neg_mul]

lemma chi_eq (x : Fin n → Bool) : chi x = (-1) ^ ones x := by
  unfold chi ones sgn
  rw [prod_ite, prod_const, prod_const, one_pow, mul_one]

/-- A function ignoring some coordinate is orthogonal to the parity character. -/
lemma corr_zero (g : (Fin n → Bool) → ℝ) (j : Fin n) (hg : Ignores g j) :
    ∑ x, g x * chi x = 0 := by
  have h := (flipEquiv j).sum_comp (fun x => g x * chi x)
  simp only [flipEquiv, Equiv.coe_fn_mk] at h
  have h2 : ∑ x, g (flipAt j x) * chi (flipAt j x) = - ∑ x, g x * chi x := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun x _ => ?_)
    rw [hg x, chi_flip, mul_neg]
  linarith

/-- The real `0/1` value of a bit. -/
def val (b : Bool) : ℝ := if b then 1 else 0

/-- **Fan-in below `n` cannot compute parity.** Let `g₁, …, gₘ` be Boolean functions on
`n ≥ 1` bits, each ignoring some coordinate, and let `α`, `T` be arbitrary reals. Then the
threshold circuit `x ↦ [∑ᵢ αᵢ gᵢ(x) ≥ T]` differs from parity at some input. -/
theorem not_parity {m : ℕ} (hn : 1 ≤ n) (g : Fin m → (Fin n → Bool) → Bool)
    (hg : ∀ i, ∃ j, Ignores (g i) j) (α : Fin m → ℝ) (T : ℝ) :
    ∃ x, decide (T ≤ ∑ i, α i * val (g i x)) ≠ parity x := by
  by_contra hcon
  push Not at hcon
  set H : (Fin n → Bool) → ℝ := fun x => ∑ i, α i * val (g i x) - T with hH
  -- `H` is orthogonal to `chi`.
  have horth : ∑ x, H x * chi x = 0 := by
    have hT : ∑ x, T * chi x = 0 :=
      corr_zero (fun _ => T) ⟨0, hn⟩ (fun _ => rfl)
    have hgi : ∀ i, ∑ x, α i * val (g i x) * chi x = 0 := by
      intro i
      obtain ⟨j, hj⟩ := hg i
      exact corr_zero (fun x => α i * val (g i x)) j (fun x => by simp only [hj x])
    simp only [hH, sub_mul, sum_sub_distrib, sum_mul]
    rw [sum_comm, sum_eq_zero (fun i _ => hgi i), hT, sub_zero]
  -- Every term is `≤ 0`, and the term at `0` is `< 0`.
  have hterm : ∀ x, H x * chi x ≤ 0 := by
    intro x
    have hx := hcon x
    rw [chi_eq]
    rcases Nat.even_or_odd (ones x) with he | ho
    · have hp : parity x = false := by
        simp [parity, Nat.even_iff.mp he]
      rw [hp, decide_eq_false_iff_not, not_le] at hx
      rw [he.neg_one_pow, mul_one]
      simp only [hH]; linarith
    · have hp : parity x = true := by
        simp [parity, Nat.odd_iff.mp ho]
      rw [hp, decide_eq_true_eq] at hx
      rw [ho.neg_one_pow, mul_neg_one]
      simp only [hH]; linarith
  have h0 : H (fun _ => false) * chi (fun _ : Fin n => false) < 0 := by
    have hx := hcon (fun _ => false)
    have hones : ones (fun _ : Fin n => false) = 0 := by simp [ones]
    have hp : parity (fun _ : Fin n => false) = false := by simp [parity, hones]
    rw [hp, decide_eq_false_iff_not, not_le] at hx
    rw [chi_eq, hones, pow_zero, mul_one]
    simp only [hH]; linarith
  have hlt : ∑ x, H x * chi x < ∑ _x : Fin n → Bool, (0 : ℝ) :=
    sum_lt_sum (fun x _ => hterm x) ⟨fun _ : Fin n => false, mem_univ _, h0⟩
  rw [sum_const_zero] at hlt
  linarith

end FaninParity

end ProblemQ
