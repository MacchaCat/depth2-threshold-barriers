import ProblemQ.NLModel

/-!
# Theorem NL-U, part 2: independence inside a row and across rows

* `card_forall_le`: events `E i` on `{0,1}^m`, where `E i` does not look at the coordinates of
  the other blocks `Pv i'` and has density `≤ p` in its own block for every fixing of the rest,
  all hold simultaneously with density `≤ p^M` (induction over the blocks).
* `card_many_idx`: `≥ q` of independent events over an arbitrary finite index type.
* The decomposition of a gate into row weights and the rest (`gateEquiv`), and the row vector
  `rvec` seen at row points.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

section Generic

variable {m : ℕ}

/-- Join a block assignment and an outside assignment. -/
def joinB (P : Finset (Fin m)) (β : {j // j ∈ P} → Bool) (γ : {j // j ∉ P} → Bool) :
    Fin m → Bool :=
  (Equiv.piEquivPiSubtypeProd (fun j => j ∈ P) (fun _ => Bool)).symm (β, γ)

lemma joinB_in (P : Finset (Fin m)) (β γ) {j : Fin m} (h : j ∈ P) :
    joinB P β γ j = β ⟨j, h⟩ := by
  simp [joinB, Equiv.piEquivPiSubtypeProd, h]

lemma joinB_out (P : Finset (Fin m)) (β γ) {j : Fin m} (h : j ∉ P) :
    joinB P β γ j = γ ⟨j, h⟩ := by
  simp [joinB, Equiv.piEquivPiSubtypeProd, h]

/-- Counting over `{0,1}^m` by splitting off a block. -/
lemma card_split (P : Finset (Fin m)) (Φ : (Fin m → Bool) → Prop) [DecidablePred Φ] :
    (univ.filter Φ).card
      = ∑ γ : {j // j ∉ P} → Bool,
          (univ.filter (fun β : {j // j ∈ P} → Bool => Φ (joinB P β γ))).card := by
  classical
  rw [← Finset.card_sigma]
  refine card_bij (fun u _ => ⟨(fun j => u j.1), (fun j => u j.1)⟩) ?_ ?_ ?_
  · intro u hu
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hu ⊢
    have : joinB P (fun j => u j.1) (fun j => u j.1) = u := by
      funext j
      by_cases h : j ∈ P
      · rw [joinB_in P _ _ h]
      · rw [joinB_out P _ _ h]
    rw [this]; exact hu
  · intro u _ u' _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    funext j
    by_cases hj : j ∈ P
    · have := congrFun (eq_of_heq h2) ⟨j, hj⟩; simpa using this
    · have := congrFun h1 ⟨j, hj⟩; simpa using this
  · rintro ⟨γ, β⟩ hb
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hb
    refine ⟨joinB P β γ, by simpa using hb, ?_⟩
    simp only [Sigma.mk.injEq]
    constructor
    · funext j; exact joinB_out P β γ j.2
    · apply heq_of_eq; funext j; exact joinB_in P β γ j.2

/-- **Independent blocks.** -/
theorem card_forall_le {M : ℕ} (Pv : Fin M → Finset (Fin m))
    (E : Fin M → (Fin m → Bool) → Prop) [∀ i, DecidablePred (E i)] {p : ℝ} (hp0 : 0 ≤ p)
    (hdep : ∀ i i', i ≠ i' → ∀ u u' : Fin m → Bool, (∀ j, j ∉ Pv i' → u j = u' j) →
      (E i u ↔ E i u'))
    (hp : ∀ i (γ : {j // j ∉ Pv i} → Bool),
      ((univ.filter (fun β : {j // j ∈ Pv i} → Bool => E i (joinB (Pv i) β γ))).card : ℝ)
        ≤ p * 2 ^ (Pv i).card) :
    ((univ.filter (fun u : Fin m → Bool => ∀ i, E i u)).card : ℝ) ≤ p ^ M * 2 ^ m := by
  classical
  suffices h : ∀ S : Finset (Fin M),
      ((univ.filter (fun u : Fin m → Bool => ∀ i ∈ S, E i u)).card : ℝ) ≤ p ^ S.card * 2 ^ m by
    have := h univ
    simpa using this
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert i₀ S hi₀ ih =>
    -- events in `S` do not look at block `i₀`
    have hS : ∀ (β β' : {j // j ∈ Pv i₀} → Bool) (γ : {j // j ∉ Pv i₀} → Bool),
        (∀ i ∈ S, E i (joinB (Pv i₀) β γ)) ↔ (∀ i ∈ S, E i (joinB (Pv i₀) β' γ)) := by
      intro β β' γ
      refine forall₂_congr (fun i hi => hdep i i₀ (fun h => hi₀ (h ▸ hi)) _ _ ?_)
      intro j hj
      rw [joinB_out _ _ _ hj, joinB_out _ _ _ hj]
    set β₀ : {j // j ∈ Pv i₀} → Bool := fun _ => false
    have h1 : ((univ.filter (fun u : Fin m → Bool => ∀ i ∈ insert i₀ S, E i u)).card : ℝ)
        = ∑ γ : {j // j ∉ Pv i₀} → Bool,
            (if ∀ i ∈ S, E i (joinB (Pv i₀) β₀ γ) then
              ((univ.filter (fun β => E i₀ (joinB (Pv i₀) β γ))).card : ℝ) else 0) := by
      rw [card_split (Pv i₀), Nat.cast_sum]
      refine sum_congr rfl (fun γ _ => ?_)
      split_ifs with hγ
      · congr 2; ext β
        simp only [mem_filter, mem_univ, true_and, forall_mem_insert]
        exact ⟨fun h => h.1, fun h => ⟨h, (hS β₀ β γ).mp hγ⟩⟩
      · norm_cast
        rw [card_eq_zero, filter_eq_empty_iff]
        intro β _ hβ
        simp only [forall_mem_insert] at hβ
        exact hγ ((hS β β₀ γ).mp hβ.2)
    have h2 : ((univ.filter (fun u : Fin m → Bool => ∀ i ∈ S, E i u)).card : ℝ)
        = ∑ γ : {j // j ∉ Pv i₀} → Bool,
            (if ∀ i ∈ S, E i (joinB (Pv i₀) β₀ γ) then (2 : ℝ) ^ (Pv i₀).card else 0) := by
      rw [card_split (Pv i₀), Nat.cast_sum]
      refine sum_congr rfl (fun γ _ => ?_)
      split_ifs with hγ
      · rw [filter_true_of_mem (fun β _ => (hS β₀ β γ).mp hγ), card_univ]
        simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
      · norm_cast
        rw [card_eq_zero, filter_eq_empty_iff]
        intro β _ hβ
        exact hγ ((hS β β₀ γ).mp hβ)
    rw [h1, card_insert_of_notMem hi₀, pow_succ, mul_comm (p ^ S.card) p, mul_assoc]
    calc ∑ γ : {j // j ∉ Pv i₀} → Bool,
          (if ∀ i ∈ S, E i (joinB (Pv i₀) β₀ γ) then
            ((univ.filter (fun β => E i₀ (joinB (Pv i₀) β γ))).card : ℝ) else 0)
        ≤ ∑ γ : {j // j ∉ Pv i₀} → Bool,
            p * (if ∀ i ∈ S, E i (joinB (Pv i₀) β₀ γ) then (2 : ℝ) ^ (Pv i₀).card else 0) := by
          refine sum_le_sum (fun γ _ => ?_)
          split_ifs
          · exact hp i₀ γ
          · simp
      _ = p * ((univ.filter (fun u : Fin m → Bool => ∀ i ∈ S, E i u)).card : ℝ) := by
          rw [h2, mul_sum]
      _ ≤ p * (p ^ S.card * 2 ^ m) := mul_le_mul_of_nonneg_left ih hp0

end Generic

section Many

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Γ] [DecidableEq Γ]

/-- `≥ q` of independent events, arbitrary index type. -/
theorem card_many_idx (q : ℕ) (E : ι → Finset Γ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ r, ((E r).card : ℝ) ≤ p * Fintype.card Γ) :
    ((univ.filter (fun x : ι → Γ => q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card : ℝ)
      ≤ ((Fintype.card ι).choose q : ℝ) * p ^ q * (Fintype.card Γ : ℝ) ^ Fintype.card ι := by
  classical
  set e := Fintype.equivFin ι
  have h := card_many_le (Γ := Γ) (Fintype.card ι) q (fun r => E (e.symm r)) hp0
    (fun r => hp _)
  have hc : (univ.filter (fun x : ι → Γ => q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card
      = (univ.filter (fun x : Fin (Fintype.card ι) → Γ =>
          q ≤ (univ.filter (fun r => x r ∈ E (e.symm r))).card)).card := by
    refine card_bij (fun x _ => fun r => x (e.symm r)) ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      calc q ≤ (univ.filter (fun r => x r ∈ E r)).card := hx
        _ = (univ.filter (fun r : Fin (Fintype.card ι) => x (e.symm r) ∈ E (e.symm r))).card := by
          refine card_bij (fun r _ => e r) ?_ ?_ ?_
          · intro r hr; simpa using hr
          · intro a _ b _ h; exact e.injective h
          · intro r hr; exact ⟨e.symm r, by simpa using hr, by simp⟩
    · intro x _ y _ h
      funext r
      have := congrFun h (e r); simpa using this
    · intro y hy
      refine ⟨fun r => y (e r), ?_, by funext r; simp⟩
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      calc q ≤ (univ.filter (fun r => y r ∈ E (e.symm r))).card := hy
        _ = (univ.filter (fun r : ι => y (e r) ∈ E r)).card := by
          refine card_bij (fun r _ => e.symm r) ?_ ?_ ?_
          · intro r hr; simpa using hr
          · intro a _ b _ h; exact e.symm.injective h
          · intro r hr; exact ⟨e r, by simpa using hr, by simp⟩
  rw [hc]
  exact h

end Many

end NLU

end

end ProblemQ
