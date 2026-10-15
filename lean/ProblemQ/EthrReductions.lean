import Mathlib

/-!
# Elementary reductions for exact-threshold circuits

These are the combinatorial steps that turn Chen–Tal–Wang's CAPP algorithm (ECCC TR26-039,
proof of Theorem 6.1, which already handles `⊕₂ ∘ DOR ∘ ETHR ∘ THR`) into an `n^{2.5−ε}` lower
bound for depth-two exact threshold circuits. All statements are pointwise identities between
integer-valued gate outputs.

* `ethr_split`: an exact threshold gate is a signed sum of two threshold gates,
  `[E = 0] = [E ≥ 0] + [−E ≥ 0] − 1`.
* `top_ethr_of_ethr`: hence an `ETHR` of `s` exact-threshold gates is an `ETHR` of `2s` threshold
  gates (same top weights, threshold shifted by `∑ αⱼ`): `ETHR ∘ ETHR (s) ⊆ ETHR ∘ THR (2s)`.
* `and_eq_zero_iff`: an `AND` of `r` exact equations with `|Eⱼ| ≤ B` is one exact equation,
  `(∀ j, Eⱼ = 0) ↔ ∑ⱼ (2B+1)^j Eⱼ = 0` (so `AND ∘ ETHR ⊆ ETHR` over the same inputs).
* `parity_ethr`: parity is computed by an `ETHR ∘ ETHR` circuit with one bottom gate
  `[|x| = j]` per odd `j ≤ n` and top `[∑ = 1]`.
-/

open Finset

namespace ProblemQ

namespace Ethr

/-- `0/1` indicator of a proposition, as an integer. -/
def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- **Exact threshold = two thresholds.** -/
lemma ethr_split (E : ℤ) : ind (E = 0) = ind (0 ≤ E) + ind (0 ≤ -E) - 1 := by
  unfold ind
  rcases lt_trichotomy E 0 with h | h | h
  · rw [if_neg h.ne, if_neg (not_le.mpr h), if_pos (by linarith)]; ring
  · subst h; simp
  · rw [if_neg h.ne', if_pos h.le, if_neg (by linarith)]; ring

/-- **`ETHR ∘ ETHR (s) ⊆ ETHR ∘ THR (2s)`.** Replacing every bottom exact-threshold gate
`[Eⱼ = 0]` by the two threshold gates `[Eⱼ ≥ 0]`, `[−Eⱼ ≥ 0]` (each with top weight `αⱼ`) and
shifting the top threshold by `∑ αⱼ` preserves the output at every input. -/
theorem top_ethr_of_ethr {s : ℕ} (α : Fin s → ℤ) (t : ℤ) (E : Fin s → ℤ) :
    (∑ j, α j * ind (E j = 0) = t) ↔
      (∑ j, (α j * ind (0 ≤ E j) + α j * ind (0 ≤ -E j)) = t + ∑ j, α j) := by
  have h : ∑ j, α j * ind (E j = 0)
      = ∑ j, (α j * ind (0 ≤ E j) + α j * ind (0 ≤ -E j)) - ∑ j, α j := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    rw [ethr_split]; ring
  rw [h]; constructor <;> intro h' <;> linarith

/-- Key estimate for base-`(2B+1)` expansions: a signed combination of lower digits is smaller
than one unit of the next digit. -/
lemma sum_lt_pow {B : ℤ} (hB : 0 ≤ B) (r : ℕ) (E : ℕ → ℤ) (hE : ∀ j, |E j| ≤ B) :
    |∑ j ∈ range r, (2 * B + 1) ^ j * E j| < (2 * B + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ]
    have hp : (0 : ℤ) ≤ (2 * B + 1) ^ r := by positivity
    have h1 : |(2 * B + 1) ^ r * E r| ≤ (2 * B + 1) ^ r * B := by
      rw [abs_mul, abs_of_nonneg hp]; exact mul_le_mul_of_nonneg_left (hE r) hp
    calc |∑ j ∈ range r, (2 * B + 1) ^ j * E j + (2 * B + 1) ^ r * E r|
        ≤ |∑ j ∈ range r, (2 * B + 1) ^ j * E j| + |(2 * B + 1) ^ r * E r| := abs_add_le _ _
      _ < (2 * B + 1) ^ r + (2 * B + 1) ^ r * B := by linarith
      _ ≤ (2 * B + 1) ^ (r + 1) := by rw [pow_succ]; nlinarith

/-- **`AND ∘ ETHR ⊆ ETHR`.** For integers with `|Eⱼ| ≤ B`, all of `E₀, …, E_{r−1}` vanish iff the
single combination `∑ⱼ (2B+1)^j Eⱼ` vanishes. -/
theorem and_eq_zero_iff {B : ℤ} (hB : 0 ≤ B) (r : ℕ) (E : ℕ → ℤ) (hE : ∀ j, |E j| ≤ B) :
    (∀ j < r, E j = 0) ↔ ∑ j ∈ range r, (2 * B + 1) ^ j * E j = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ]
    constructor
    · intro h
      have h1 : ∑ j ∈ range r, (2 * B + 1) ^ j * E j = 0 :=
        ih.mp (fun j hj => h j (Nat.lt_succ_of_lt hj))
      rw [h1, h r (Nat.lt_succ_self r)]; ring
    · intro h
      have hlow := sum_lt_pow hB r E hE
      -- the top digit must vanish, otherwise it dominates the lower ones
      have hr : E r = 0 := by
        by_contra hne
        have hp : (0 : ℤ) < (2 * B + 1) ^ r := by positivity
        have hge : (2 * B + 1) ^ r ≤ |(2 * B + 1) ^ r * E r| := by
          rw [abs_mul, abs_of_pos hp]
          have : (1 : ℤ) ≤ |E r| := Int.one_le_abs hne
          nlinarith
        have : ∑ j ∈ range r, (2 * B + 1) ^ j * E j = -((2 * B + 1) ^ r * E r) := by linarith
        rw [this, abs_neg] at hlow
        linarith
      rw [hr, mul_zero, add_zero] at h
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact ih.mpr h j hj
      · rw [hj]; exact hr

/-- Hamming weight. -/
def wt {n : ℕ} (x : Fin n → Bool) : ℕ := #(univ.filter (fun i => x i = true))

/-- **Parity in `ETHR ∘ ETHR`.** With bottom gates `[|x| = j]` for the odd `j ≤ n` (each an exact
threshold of the inputs) and top gate `[∑ = 1]`, the circuit computes parity. -/
theorem parity_ethr {n : ℕ} (x : Fin n → Bool) :
    (∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = 1), ind (wt x = j) = 1) ↔ wt x % 2 = 1 := by
  have hw : wt x ≤ n := by
    unfold wt; exact (card_filter_le _ _).trans (by simp)
  rw [show (∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = 1), ind (wt x = j))
      = ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = 1), (if wt x = j then 1 else 0) from rfl]
  rw [sum_ite_eq]
  simp only [mem_filter, mem_range]
  constructor
  · intro h
    by_contra hc
    rw [if_neg (fun hh => hc hh.2)] at h
    exact absurd h (by norm_num)
  · intro h
    rw [if_pos ⟨Nat.lt_succ_of_le hw, h⟩]

end Ethr

end ProblemQ
