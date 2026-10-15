import ProblemQ.Restrict

/-!
# The per-point step of Theorems NL / NL-U

A list entry is an `(m+1)`-output function `P` of the gate vector `u ∈ {0,1}^m` whose outputs
have F₂-degree `≤ d` (literals are absorbed: `P` may be any such family for fixed literals).
It is *correct* at `u` if it outputs `1hotSUM(u)`.

`point_bound`: if all gates outside a set `Pset` of size `F` are fixed (to `u₀`) and the gates in
`Pset` carry fair coins `β`, then `P` is correct for at most a `½ + (d+1)/√F` fraction of `β`.
Proof: the derived threshold polynomial `Σ_{s ≥ θ} P_s` has degree `≤ d`, equals the median
threshold of `β` wherever `P` is correct (with `θ = #fixed ones + ⌈F/2⌉`), restricts to a
degree-`≤ d` function of `β` (`restrict_mem`), and Smolensky (`smolensky_prob`) applies.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace Smolensky

variable {m : ℕ}

/-- Number of ones of a gate vector. -/
def count (u : Fin m → Bool) : ℕ := (ones u).card

lemma count_le (u : Fin m → Bool) : count u ≤ m := by
  unfold count
  calc (ones u).card ≤ (univ : Finset (Fin m)).card := card_le_card (subset_univ _)
    _ = m := by simp

/-- Correctness of an `(m+1)`-output entry at `u`: it outputs `1hotSUM(u)`. -/
def Correct (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2) (u : Fin m → Bool) : Prop :=
  ∀ s : Fin (m + 1), P u s = if count u = s.val then 1 else 0

instance (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2) (u : Fin m → Bool) :
    Decidable (Correct P u) := by unfold Correct; infer_instance

lemma mem_ones {k : ℕ} (u : Fin k → Bool) (g : Fin k) : g ∈ ones u ↔ u g = true := by
  simp [ones]

/-- The derived threshold function `Σ_{s ≥ θ} P_s`. -/
def derived (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2) (θ : ℕ) (u : Fin m → Bool) : ZMod 2 :=
  ∑ s ∈ univ.filter (fun s : Fin (m + 1) => θ ≤ s.val), P u s

lemma derived_mem {d : ℕ} (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ s, (fun u => P u s) ∈ V d) (θ : ℕ) : derived P θ ∈ V d := by
  have : derived P θ = ∑ s ∈ univ.filter (fun s : Fin (m + 1) => θ ≤ s.val),
      (fun u => P u s) := by
    funext u; rw [Finset.sum_apply]; rfl
  rw [this]
  exact Submodule.sum_mem _ (fun s _ => hP s)

lemma derived_correct (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2) (u : Fin m → Bool)
    (h : Correct P u) (θ : ℕ) : derived P θ u = if θ ≤ count u then 1 else 0 := by
  classical
  unfold derived
  unfold Correct at h
  simp_rw [h]
  rw [← sum_filter]
  set s₀ : Fin (m + 1) := ⟨count u, Nat.lt_succ_of_le (count_le u)⟩
  have hfil : (univ.filter (fun s : Fin (m + 1) => θ ≤ s.val)).filter
      (fun s => count u = s.val) = if θ ≤ count u then {s₀} else ∅ := by
    ext s
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with hθ
    · simp only [mem_singleton]
      constructor
      · rintro ⟨_, hs⟩; exact Fin.ext hs.symm
      · rintro rfl; exact ⟨hθ, rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro h1 h2; rw [h2] at hθ; exact hθ h1
  rw [hfil]
  split_ifs <;> simp

variable {F : ℕ}

/-- Enumeration of `Pset` as an embedding. -/
def embP (Pset : Finset (Fin m)) (e : Fin F ≃ Pset) : Fin F ↪ Fin m :=
  ⟨fun j => (e j : Fin m), fun a b h => e.injective (Subtype.ext h)⟩

@[simp] lemma embP_apply (Pset : Finset (Fin m)) (e : Fin F ≃ Pset) (j : Fin F) :
    embP Pset e j = (e j : Fin m) := rfl

lemma ones_embed (Pset : Finset (Fin m)) (e : Fin F ≃ Pset) (u₀ : Fin m → Bool)
    (β : Fin F → Bool) :
    count (embed Pset e u₀ β) = ((ones u₀).filter (fun g => g ∉ Pset)).card + (ones β).card := by
  classical
  unfold count
  have hsplit : ones (embed Pset e u₀ β)
      = (ones u₀).filter (fun g => g ∉ Pset) ∪ (ones β).map (embP Pset e) := by
    ext g
    rw [mem_union, mem_filter, mem_map, mem_ones, mem_ones]
    unfold embed
    by_cases hg : g ∈ Pset
    · rw [dif_pos hg]
      constructor
      · intro h; right; exact ⟨e.symm ⟨g, hg⟩, (mem_ones _ _).mpr h, by rw [embP_apply]; simp⟩
      · rintro (⟨_, h⟩ | ⟨j, hj, hjg⟩)
        · exact absurd hg h
        · rw [mem_ones] at hj
          have : e.symm ⟨g, hg⟩ = j := by
            apply e.injective; apply Subtype.ext; rw [embP_apply] at hjg; simp [← hjg]
          rw [this]; exact hj
    · rw [dif_neg hg]
      constructor
      · intro h; exact Or.inl ⟨h, hg⟩
      · rintro (⟨h, _⟩ | ⟨j, _, hjg⟩)
        · exact h
        · exact absurd (hjg ▸ (e j).2) hg
  rw [hsplit, card_union_of_disjoint, card_map]
  rw [disjoint_left]
  intro g hg hg'
  rw [mem_filter] at hg
  rw [mem_map] at hg'
  obtain ⟨j, _, hjg⟩ := hg'
  exact hg.2 (hjg ▸ (e j).2)

/-- **Per-point bound.** -/
theorem point_bound (hF : 1 ≤ F) {d : ℕ} (P : (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ s, (fun u => P u s) ∈ V d) (Pset : Finset (Fin m)) (e : Fin F ≃ Pset)
    (u₀ : Fin m → Bool) :
    ((univ.filter (fun β : Fin F → Bool => Correct P (embed Pset e u₀ β))).card : ℝ) / 2 ^ F
      ≤ 1 / 2 + (d + 1) / Real.sqrt F := by
  classical
  set c₀ := ((ones u₀).filter (fun g => g ∉ Pset)).card
  set θ := c₀ + (F - F / 2)
  set Q : (Fin F → Bool) → ZMod 2 := fun β => derived P θ (embed Pset e u₀ β)
  have hQ : Q ∈ V (F := F) d := restrict_mem Pset e u₀ (derived_mem P hP θ)
  have hsub : univ.filter (fun β : Fin F → Bool => Correct P (embed Pset e u₀ β))
      ⊆ univ.filter (fun β : Fin F → Bool => Q β = TH β) := by
    intro β hβ
    simp only [mem_filter, mem_univ, true_and] at hβ ⊢
    show derived P θ (embed Pset e u₀ β) = TH β
    rw [derived_correct P _ hβ θ, ones_embed]
    unfold TH
    congr 1
    apply propext
    constructor <;> intro h <;> omega
  have h1 := smolensky_prob hF hQ
  have h2 : ((univ.filter (fun β : Fin F → Bool => Correct P (embed Pset e u₀ β))).card : ℝ)
      ≤ ((univ.filter (fun β : Fin F → Bool => Q β = TH β)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  calc _ ≤ ((univ.filter (fun β : Fin F → Bool => Q β = TH β)).card : ℝ) / 2 ^ F := by
        gcongr
    _ ≤ _ := h1

end Smolensky

end

end ProblemQ

namespace ProblemQ

noncomputable section

/-- **Row lemma (abstract).** Coins of a row split as `(ρ, β)` with private blocks `β i`; if
for every `ρ` the event "point `i` correct" depends only on `(ρ, β i)` and has density `≤ p` in
`β i`, then at least `q` of the `M` points are correct with density `≤ C(M,q) p^q`. -/
theorem row_bound {M : ℕ} {F : Fin M → ℕ} (Rest : Type*) [Fintype Rest] [DecidableEq Rest]
    (good : ∀ i, Rest → (Fin (F i) → Bool) → Prop) [∀ i ρ β, Decidable (good i ρ β)]
    {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ i ρ, ((univ.filter (fun β => good i ρ β)).card : ℝ) ≤ p * 2 ^ F i) (q : ℕ) :
    ((univ.filter (fun x : Rest × (∀ i, Fin (F i) → Bool) =>
        q ≤ (univ.filter (fun i => good i x.1 (x.2 i))).card)).card : ℝ)
      ≤ (M.choose q : ℝ) * p ^ q * (Fintype.card Rest * ∏ i, (2 : ℝ) ^ F i) := by
  classical
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type]
  have hρ : ∀ ρ : Rest, (∑ β : (∀ i, Fin (F i) → Bool),
      if q ≤ (univ.filter (fun i => good i ρ (β i))).card then ((1 : ℕ) : ℝ) else 0)
        ≤ (M.choose q : ℝ) * p ^ q * ∏ i, (2 : ℝ) ^ F i := by
    intro ρ
    have h := card_many_le_dep (Γ := fun i => Fin (F i) → Bool) q
      (fun i => univ.filter (fun β => good i ρ β)) hp0 (fun i => by
        simpa [Fintype.card_fun, Fintype.card_bool] using hp i ρ)
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] at h
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter] at h
    simpa [mem_filter] using h
  calc ∑ ρ : Rest, ∑ β : (∀ i, Fin (F i) → Bool),
        (if q ≤ (univ.filter (fun i => good i ρ (β i))).card then ((1 : ℕ) : ℝ) else 0)
      ≤ ∑ _ρ : Rest, (M.choose q : ℝ) * p ^ q * ∏ i, (2 : ℝ) ^ F i := sum_le_sum (fun ρ _ => hρ ρ)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

end

end ProblemQ
