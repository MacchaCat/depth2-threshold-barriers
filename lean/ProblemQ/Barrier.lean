import ProblemQ.Circuit

/-!
# Union bound and Markov: from columns to whole schemes

An oblivious list consists of `L` coefficient vectors `α a` and center rules `c a I`.
A circuit `ω` is *broken* by the list if for some live set `I` of size `k`, at least half of
the columns `z` are certified by some list entry.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

variable {n m L : ℕ} (T : Finset ℤ)

/-- Fraction of columns (outside assignments) certified by some list entry. -/
def certFrac (ω : Fin m → Gate n T) (α : Fin L → Fin m → ℝ)
    (c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) (I : Finset (Fin n)) (W δ : ℝ) : ℝ :=
  ((univ.filter (fun z : Fin n → Bool => ∃ a, certified T ω (α a) I z (c a I) W δ)).card : ℝ)
    / 2 ^ n

/-- The list succeeds on `ω` for some live set of size `k`. -/
def succeeds (k : ℕ) (ω : Fin m → Gate n T) (α : Fin L → Fin m → ℝ)
    (c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) (W δ : ℝ) : Prop :=
  ∃ I : Finset (Fin n), I.card = k ∧ 1 / 2 ≤ certFrac T ω α c I W δ

open Classical in
/-- **Union bound + Markov.** If every (column, entry) is certified by at most a `B` fraction of
circuits, the list succeeds on at most a `2 · C(n,k) · L · B` fraction of circuits. -/
theorem succeeds_bound (k : ℕ) (α : Fin L → Fin m → ℝ)
    (c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) (W δ B : ℝ)
    (hB : ∀ I : Finset (Fin n), I.card = k → ∀ z a,
      ((univ.filter (fun ω : Fin m → Gate n T => certified T ω (α a) I z (c a I) W δ)).card : ℝ)
        ≤ B * (Fintype.card (Gate n T) : ℝ) ^ m) :
    ((univ.filter (fun ω : Fin m → Gate n T => succeeds T k ω α c W δ)).card : ℝ)
      ≤ 2 * (n.choose k) * L * B * (Fintype.card (Gate n T) : ℝ) ^ m := by
  set Ω := Fin m → Gate n T
  set G : ℝ := (Fintype.card (Gate n T) : ℝ) ^ m
  -- for a fixed I, Markov
  have hI : ∀ I : Finset (Fin n), I.card = k →
      ((univ.filter (fun ω : Ω => 1 / 2 ≤ certFrac T ω α c I W δ)).card : ℝ) ≤ 2 * L * B * G := by
    intro I hIk
    have hmarkov : ((univ.filter (fun ω : Ω => 1 / 2 ≤ certFrac T ω α c I W δ)).card : ℝ)
        ≤ 2 * ∑ ω : Ω, certFrac T ω α c I W δ := by
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, mul_sum]
      refine sum_le_sum (fun ω _ => ?_)
      have h0 : 0 ≤ certFrac T ω α c I W δ := by unfold certFrac; positivity
      split_ifs with h
      · push_cast; linarith
      · push_cast; linarith
    have hsum : ∑ ω : Ω, certFrac T ω α c I W δ ≤ L * B * G := by
      unfold certFrac
      rw [← sum_div, div_le_iff₀ (by positivity)]
      -- swap ω and z
      have : ∑ ω : Ω, ((univ.filter (fun z : Fin n → Bool =>
            ∃ a, certified T ω (α a) I z (c a I) W δ)).card : ℝ)
          = ∑ z : Fin n → Bool, ((univ.filter (fun ω : Ω =>
            ∃ a, certified T ω (α a) I z (c a I) W δ)).card : ℝ) := by
        simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
        rw [sum_comm]
      rw [this]
      have hz : ∀ z : Fin n → Bool, ((univ.filter (fun ω : Ω =>
            ∃ a, certified T ω (α a) I z (c a I) W δ)).card : ℝ) ≤ L * (B * G) := by
        intro z
        have hU : univ.filter (fun ω : Ω => ∃ a, certified T ω (α a) I z (c a I) W δ)
            = univ.biUnion (fun a => univ.filter
                (fun ω : Ω => certified T ω (α a) I z (c a I) W δ)) := by
          ext ω; simp
        rw [hU]
        calc ((univ.biUnion (fun a => univ.filter
                (fun ω : Ω => certified T ω (α a) I z (c a I) W δ))).card : ℝ)
            ≤ ∑ a : Fin L, ((univ.filter
                (fun ω : Ω => certified T ω (α a) I z (c a I) W δ)).card : ℝ) := by
              exact_mod_cast card_biUnion_le
          _ ≤ ∑ _a : Fin L, B * G := sum_le_sum (fun a _ => hB I hIk z a)
          _ = L * (B * G) := by simp
      calc ∑ z : Fin n → Bool, ((univ.filter (fun ω : Ω =>
            ∃ a, certified T ω (α a) I z (c a I) W δ)).card : ℝ)
          ≤ ∑ _z : Fin n → Bool, (L : ℝ) * (B * G) := sum_le_sum (fun z _ => hz z)
        _ = L * B * G * 2 ^ n := by
            simp [Fintype.card_fun, Fintype.card_bool]; ring
    linarith
  -- union over I
  have hU : univ.filter (fun ω : Ω => succeeds T k ω α c W δ)
      = (univ.filter (fun I : Finset (Fin n) => I.card = k)).biUnion
          (fun I => univ.filter (fun ω : Ω => 1 / 2 ≤ certFrac T ω α c I W δ)) := by
    ext ω; simp [succeeds]
  rw [hU]
  calc (((univ.filter (fun I : Finset (Fin n) => I.card = k)).biUnion
          (fun I => univ.filter (fun ω : Ω => 1 / 2 ≤ certFrac T ω α c I W δ))).card : ℝ)
      ≤ ∑ I ∈ univ.filter (fun I : Finset (Fin n) => I.card = k),
          ((univ.filter (fun ω : Ω => 1 / 2 ≤ certFrac T ω α c I W δ)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _I ∈ univ.filter (fun I : Finset (Fin n) => I.card = k), 2 * L * B * G :=
        sum_le_sum (fun I hI' => hI I (by simpa using hI'))
    _ = 2 * (n.choose k) * L * B * G := by
        rw [sum_const, nsmul_eq_mul]
        have : (univ.filter (fun I : Finset (Fin n) => I.card = k)).card = n.choose k := by
          have hE : univ.filter (fun I : Finset (Fin n) => I.card = k) = powersetCard k univ := by
            ext I; simp [mem_powersetCard_univ]
          rw [hE, card_powersetCard, card_univ, Fintype.card_fin]
        rw [this]; ring

end

end ProblemQ
