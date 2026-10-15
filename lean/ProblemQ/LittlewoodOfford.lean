import Mathlib.Combinatorics.SetFamily.LYM
import ProblemQ.Rows

/-!
# Littlewood–Offord via Sperner

The anti-concentration side of the CAPP route rests on Erdős's argument:

* `card_window_le`: if `f : Finset α → ℤ` is strictly monotone (`s ⊂ t → f s < f t`), then each
  level set is an antichain, so by Sperner a window `[c, c + Δ)` contains at most
  `Δ · C(n, ⌊n/2⌋)` sets (`n = |α|`).
* `window_prob_le`: hence the window has probability at most `Δ / √n` under the uniform measure.
* `erdos_lo`: **Erdős–Littlewood–Offord.** For nonzero integer weights `a`, the number of
  `y ∈ {0,1}^k` with `∑ aᵢ yᵢ ∈ [c, c + Δ)` is at most `Δ · C(k, ⌊k/2⌋)`. Flipping the coordinates
  with negative weight makes the sum strictly monotone in the set of ones.
-/

open Finset

namespace ProblemQ

namespace LO

section Mono

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Level sets of a strictly monotone function are antichains. -/
lemma level_antichain (f : Finset α → ℤ) (hf : ∀ s t, s ⊂ t → f s < f t) (c : ℤ) :
    IsAntichain (· ⊆ ·) (SetLike.coe (univ.filter (fun s => f s = c))) := by
  intro s hs t ht hne hst
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  have := hf s t (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
  omega

/-- **Window bound for strictly monotone functions.** -/
theorem card_window_le (f : Finset α → ℤ) (hf : ∀ s t, s ⊂ t → f s < f t) (c : ℤ) (Δ : ℕ) :
    #(univ.filter (fun s => c ≤ f s ∧ f s < c + Δ))
      ≤ Δ * (Fintype.card α).choose (Fintype.card α / 2) := by
  have hsub : univ.filter (fun s => c ≤ f s ∧ f s < c + Δ)
      ⊆ (range Δ).biUnion (fun j => univ.filter (fun s => f s = c + j)) := by
    intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    refine ⟨(f s - c).toNat, ?_, ?_⟩ <;> omega
  calc #(univ.filter (fun s => c ≤ f s ∧ f s < c + Δ))
      ≤ #((range Δ).biUnion (fun j => univ.filter (fun s => f s = c + j))) := card_le_card hsub
    _ ≤ ∑ j ∈ range Δ, #(univ.filter (fun s => f s = c + j)) := card_biUnion_le
    _ ≤ ∑ _j ∈ range Δ, (Fintype.card α).choose (Fintype.card α / 2) :=
        sum_le_sum (fun j _ => (level_antichain f hf (c + j)).sperner)
    _ = Δ * (Fintype.card α).choose (Fintype.card α / 2) := by
        rw [sum_const, card_range, smul_eq_mul]

/-- **Probability form**: a window of width `Δ` has probability at most `Δ / √n`. -/
theorem window_prob_le (f : Finset α → ℤ) (hf : ∀ s t, s ⊂ t → f s < f t) (c : ℤ) (Δ : ℕ)
    (hn : 1 ≤ Fintype.card α) :
    (#(univ.filter (fun s => c ≤ f s ∧ f s < c + Δ)) : ℝ) / 2 ^ Fintype.card α
      ≤ Δ / Real.sqrt (Fintype.card α) := by
  set n := Fintype.card α
  have h1 := card_window_le f hf c Δ
  have h2 := choose_half_sq_mul_le n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  -- C(n, n/2) * √n ≤ 2^n
  have hc : (n.choose (n / 2) : ℝ) * Real.sqrt n ≤ 2 ^ n := by
    have : ((n.choose (n / 2) : ℝ) * Real.sqrt n) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn'.le, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
      exact_mod_cast h2
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  have h1' : (#(univ.filter (fun s => c ≤ f s ∧ f s < c + Δ)) : ℝ)
      ≤ Δ * (n.choose (n / 2) : ℝ) := by exact_mod_cast h1
  rw [div_le_div_iff₀ h2n hs]
  calc (#(univ.filter (fun s => c ≤ f s ∧ f s < c + Δ)) : ℝ) * Real.sqrt n
      ≤ Δ * (n.choose (n / 2) : ℝ) * Real.sqrt n := by gcongr
    _ = Δ * ((n.choose (n / 2) : ℝ) * Real.sqrt n) := by ring
    _ ≤ Δ * 2 ^ n := by gcongr

end Mono

section Linear

variable {k : ℕ}

/-- `y` as an integer `0/1` vector. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Flip the coordinates with negative weight: `ones` of the flipped vector. -/
def flipSet (a : Fin k → ℤ) (y : Fin k → Bool) : Finset (Fin k) :=
  univ.filter (fun i => (y i = true) ≠ (a i < 0))

/-- The linear form, rewritten through the flipped set: a constant plus `∑_{i ∈ s} |aᵢ|`. -/
lemma lin_eq (a : Fin k → ℤ) (y : Fin k → Bool) :
    ∑ i, a i * bit (y i)
      = ∑ i, (if a i < 0 then a i else 0) + ∑ i ∈ flipSet a y, |a i| := by
  rw [flipSet, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  unfold bit
  rcases lt_or_ge (a i) 0 with ha | ha
  · cases y i <;> simp [ha, abs_of_neg ha]
  · have : ¬ a i < 0 := not_lt.mpr ha
    cases y i <;> simp [this, abs_of_nonneg ha]

lemma flipSet_injective (a : Fin k → ℤ) : Function.Injective (flipSet a) := by
  intro y y' h
  funext i
  have := congrArg (fun s => i ∈ s) h
  simp only [flipSet, mem_filter, mem_univ, true_and, eq_iff_iff] at this
  by_cases ha : a i < 0 <;> cases hy : y i <;> cases hy' : y' i <;> simp_all

/-- **Erdős–Littlewood–Offord.** For nonzero integer weights, a window of width `Δ` contains at
most `Δ · C(k, ⌊k/2⌋)` of the `2^k` points. -/
theorem erdos_lo (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0) (c : ℤ) (Δ : ℕ) :
    #(univ.filter (fun y : Fin k → Bool => c ≤ ∑ i, a i * bit (y i) ∧ ∑ i, a i * bit (y i) < c + Δ))
      ≤ Δ * k.choose (k / 2) := by
  set C0 := ∑ i, (if a i < 0 then a i else 0)
  set g : Finset (Fin k) → ℤ := fun s => ∑ i ∈ s, |a i|
  have hg : ∀ s t, s ⊂ t → g s < g t := by
    intro s t hst
    obtain ⟨j, hjt, hjs⟩ := exists_of_ssubset hst
    have hsub : insert j s ⊆ t := insert_subset hjt hst.subset
    have h1 : g (insert j s) ≤ g t :=
      sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg _)
    have h2 : g (insert j s) = |a j| + g s := sum_insert hjs
    have h3 : 0 < |a j| := abs_pos.mpr (ha j)
    linarith
  have hw := card_window_le g hg (c - C0) Δ
  rw [Fintype.card_fin] at hw
  refine le_trans ?_ hw
  refine card_le_card_of_injOn (flipSet a) ?_ (fun y _ y' _ h => flipSet_injective a h)
  intro y hy
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
  rw [lin_eq] at hy
  have e : g (flipSet a y) = ∑ i ∈ flipSet a y, |a i| := rfl
  constructor <;> omega

end Linear

end LO

end ProblemQ
