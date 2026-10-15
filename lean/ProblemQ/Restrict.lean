import ProblemQ.Rows

/-!
# More building blocks for Theorem NL-U

* `card_many_le_dep`: the independent-events counting lemma for heterogeneous coordinates
  `x : ∀ r, Γ r` (the private coin blocks of a row have different sizes).
* `restrict_mem`: fixing all variables outside a set `P` of a degree-`≤ d` function on
  `{0,1}^m` leaves a degree-`≤ d` function of the variables in `P`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

section RowsDep

variable {R : ℕ} {Γ : Fin R → Type*} [∀ r, Fintype (Γ r)] [∀ r, DecidableEq (Γ r)]

lemma card_hit_all_dep (E : ∀ r, Finset (Γ r)) (T : Finset (Fin R)) :
    ((univ.filter (fun x : (∀ r, Γ r) => ∀ r ∈ T, x r ∈ E r)).card : ℝ)
      = ∏ r, (if r ∈ T then ((E r).card : ℝ) else (Fintype.card (Γ r) : ℝ)) := by
  classical
  have hP := Fintype.prod_sum (fun (r : Fin R) (γ : Γ r) =>
    if r ∈ T then (if γ ∈ E r then (1 : ℝ) else 0) else 1)
  have hl : ∀ x : (∀ r, Γ r), ∏ r, (if r ∈ T then (if x r ∈ E r then (1 : ℝ) else 0) else 1)
      = if ∀ r ∈ T, x r ∈ E r then 1 else 0 := by
    intro x
    split_ifs with h
    · exact prod_eq_one (fun r _ => by split_ifs with h1 h2 <;> simp_all)
    · push Not at h
      obtain ⟨r, hr, hx⟩ := h
      exact prod_eq_zero (mem_univ r) (by simp [hr, hx])
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  simp only [Nat.cast_one]
  rw [← sum_congr rfl (fun x _ => hl x), ← hP]
  refine prod_congr rfl (fun r _ => ?_)
  split_ifs with h
  · rw [← sum_filter]; simp
  · simp

/-- **Many independent events, heterogeneous coordinates.** -/
theorem card_many_le_dep (q : ℕ) (E : ∀ r, Finset (Γ r)) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ r, ((E r).card : ℝ) ≤ p * Fintype.card (Γ r)) :
    ((univ.filter (fun x : (∀ r, Γ r) =>
        q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card : ℝ)
      ≤ (R.choose q : ℝ) * p ^ q * ∏ r, (Fintype.card (Γ r) : ℝ) := by
  classical
  have hsub : univ.filter (fun x : (∀ r, Γ r) => q ≤ (univ.filter (fun r => x r ∈ E r)).card)
      ⊆ (univ.powersetCard q).biUnion
          (fun T => univ.filter (fun x : (∀ r, Γ r) => ∀ r ∈ T, x r ∈ E r)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hx
    rw [mem_biUnion]
    refine ⟨T, mem_powersetCard.mpr ⟨subset_univ _, hTc⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro r hr
    simpa using hT hr
  have hone : ∀ T ∈ (univ : Finset (Fin R)).powersetCard q,
      ((univ.filter (fun x : (∀ r, Γ r) => ∀ r ∈ T, x r ∈ E r)).card : ℝ)
        ≤ p ^ q * ∏ r, (Fintype.card (Γ r) : ℝ) := by
    intro T hT
    have hTc : T.card = q := (mem_powersetCard.mp hT).2
    rw [card_hit_all_dep]
    calc ∏ r, (if r ∈ T then ((E r).card : ℝ) else (Fintype.card (Γ r) : ℝ))
        ≤ ∏ r, (if r ∈ T then p else 1) * (Fintype.card (Γ r) : ℝ) := by
          apply prod_le_prod₀
          · intro r _; split_ifs <;> positivity
          · intro r _; split_ifs
            · exact hp r
            · simp
      _ = p ^ q * ∏ r, (Fintype.card (Γ r) : ℝ) := by
          rw [prod_mul_distrib, prod_ite, prod_const, prod_const, one_pow, mul_one,
            filter_mem_eq_inter, univ_inter, hTc]
  calc ((univ.filter (fun x : (∀ r, Γ r) =>
          q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card : ℝ)
      ≤ (((univ.powersetCard q).biUnion
          (fun T => univ.filter (fun x : (∀ r, Γ r) => ∀ r ∈ T, x r ∈ E r))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ T ∈ (univ : Finset (Fin R)).powersetCard q,
          ((univ.filter (fun x : (∀ r, Γ r) => ∀ r ∈ T, x r ∈ E r)).card : ℝ) := by
        rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
    _ ≤ ∑ _T ∈ (univ : Finset (Fin R)).powersetCard q,
          p ^ q * ∏ r, (Fintype.card (Γ r) : ℝ) := sum_le_sum hone
    _ = (R.choose q : ℝ) * p ^ q * ∏ r, (Fintype.card (Γ r) : ℝ) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end RowsDep

namespace Smolensky

section Restrict

variable {m F : ℕ}

/-- Fill the variables of `P` (enumerated by `e`) from `β`, the others from `u₀`. -/
def embed (P : Finset (Fin m)) (e : Fin F ≃ P) (u₀ : Fin m → Bool) (β : Fin F → Bool) :
    Fin m → Bool :=
  fun g => if h : g ∈ P then β (e.symm ⟨g, h⟩) else u₀ g

lemma mono_embed (P : Finset (Fin m)) (e : Fin F ≃ P) (u₀ : Fin m → Bool)
    (M : Finset (Fin m)) :
    (fun β => mono M (embed P e u₀ β))
      = (if ∀ g ∈ M, g ∉ P → u₀ g = true then (1 : ZMod 2) else 0) •
          mono ((univ : Finset (Fin F)).filter (fun j => (e j : Fin m) ∈ M)) := by
  classical
  funext β
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold mono embed
  by_cases hout : ∀ g ∈ M, g ∉ P → u₀ g = true
  · rw [if_pos hout, one_mul]
    congr 1
    apply propext
    constructor
    · intro h j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      have := h _ hj
      simpa [(e j).2] using this
    · intro h g hg
      by_cases hgP : g ∈ P
      · simp only [hgP, dite_true]
        apply h
        simp only [mem_filter, mem_univ, true_and]
        simpa using hg
      · simp only [hgP, dite_false]; exact hout g hg hgP
  · rw [if_neg hout, zero_mul]
    push Not at hout
    obtain ⟨g, hg, hgP, hu⟩ := hout
    rw [if_neg]
    push Not
    exact ⟨g, hg, by simp [hgP, hu]⟩

/-- **Restriction preserves degree.** -/
theorem restrict_mem (P : Finset (Fin m)) (e : Fin F ≃ P) (u₀ : Fin m → Bool) {d : ℕ}
    {f : (Fin m → Bool) → ZMod 2} (hf : f ∈ V d) :
    (fun β => f (embed P e u₀ β)) ∈ V (F := F) d := by
  classical
  let φ : ((Fin m → Bool) → ZMod 2) →ₗ[ZMod 2] ((Fin F → Bool) → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (embed P e u₀)
  have hle : V (F := m) d ≤ (V (F := F) d).comap φ := by
    unfold V
    apply Submodule.span_le.mpr
    intro f hf
    obtain ⟨M, hM, rfl⟩ := mem_gens.mp (Finset.mem_coe.mp hf)
    show φ (mono M) ∈ V d
    have : φ (mono M) = fun β => mono M (embed P e u₀ β) := rfl
    rw [this, mono_embed]
    refine Submodule.smul_mem _ _ (mono_mem ?_)
    calc ((univ : Finset (Fin F)).filter (fun j => (e j : Fin m) ∈ M)).card
        ≤ M.card := by
          refine card_le_card_of_injOn (fun j => (e j : Fin m)) ?_ ?_
          · intro j hj; simpa using hj
          · intro a _ b _ h; exact e.injective (Subtype.ext h)
      _ ≤ d := hM
  exact hle hf

end Restrict

end Smolensky

end

end ProblemQ
