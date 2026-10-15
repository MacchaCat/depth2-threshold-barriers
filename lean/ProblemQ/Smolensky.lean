import Mathlib

/-!
# Smolensky's lemma at an exact median

Let `Q : {0,1}^F → F₂` lie in the span of multilinear monomials of degree `≤ d`, and let
`TH(β) = 1[|β| ≥ ⌈F/2⌉]`. Then `Q` agrees with `TH` on at most `#{M ⊆ [F] : |M| ≤ ⌊F/2⌋ + d}`
points. This is the core of Theorem NL (non-linear certificates): a degree-`d` polynomial over
fair coins predicts their majority with advantage `O(d/√F)` only.

Proof: every function equals `g₀ + TH·(g₀ + g₁)` with `deg gᵢ ≤ ⌊F/2⌋` (Möbius interpolation on the
lower half, and on the upper half after complementing). On the agreement set replace `TH` by `Q`,
so every function on that set has degree `≤ ⌊F/2⌋ + d`; count dimensions.
-/

open Finset BigOperators

namespace ProblemQ

namespace Smolensky

variable {F : ℕ}

/-- The multilinear monomial `∏_{i∈M} βᵢ` as a function on the cube. -/
def mono (M : Finset (Fin F)) (β : Fin F → Bool) : ZMod 2 :=
  if ∀ i ∈ M, β i = true then 1 else 0

/-- Generators of degree `≤ D`. -/
def gens (D : ℕ) : Finset ((Fin F → Bool) → ZMod 2) :=
  (univ.filter (fun M : Finset (Fin F) => M.card ≤ D)).image mono

/-- Functions of degree `≤ D`. -/
def V (D : ℕ) : Submodule (ZMod 2) ((Fin F → Bool) → ZMod 2) :=
  Submodule.span (ZMod 2) ((gens (F := F) D : Finset _) : Set ((Fin F → Bool) → ZMod 2))

/-- Indicator vector of a set. -/
def ind (N : Finset (Fin F)) : Fin F → Bool := fun i => decide (i ∈ N)

/-- Set of ones. -/
def ones (β : Fin F → Bool) : Finset (Fin F) := univ.filter (fun i => β i = true)

lemma mono_eq (M : Finset (Fin F)) (β : Fin F → Bool) :
    mono M β = if M ⊆ ones β then 1 else 0 := by
  unfold mono ones
  congr 1
  apply propext
  constructor
  · intro h i hi; simp [h i hi]
  · intro h i hi; simpa using h hi

lemma mem_gens {D : ℕ} {f : (Fin F → Bool) → ZMod 2} :
    f ∈ gens D ↔ ∃ M : Finset (Fin F), M.card ≤ D ∧ mono M = f := by
  simp [gens]

lemma mono_mem {D : ℕ} {M : Finset (Fin F)} (hM : M.card ≤ D) : mono M ∈ V D :=
  Submodule.subset_span (Finset.mem_coe.mpr (mem_gens.mpr ⟨M, hM, rfl⟩))

lemma V_mono {D D' : ℕ} (h : D ≤ D') : V (F := F) D ≤ V D' := by
  unfold V
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨M, hM, rfl⟩ := mem_gens.mp (Finset.mem_coe.mp hf)
  exact mono_mem (hM.trans h)

lemma mono_mul (M N : Finset (Fin F)) : mono M * mono N = mono (M ∪ N) := by
  funext β
  simp only [Pi.mul_apply, mono_eq, union_subset_iff]
  split_ifs <;> simp_all

lemma mul_mem {a b : ℕ} {f g : (Fin F → Bool) → ZMod 2} (hf : f ∈ V a) (hg : g ∈ V b) :
    f * g ∈ V (a + b) := by
  have hle : V (F := F) a * V b ≤ V (a + b) := by
    unfold V
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, q, hq, rfl⟩
    obtain ⟨M, hM, rfl⟩ := mem_gens.mp (Finset.mem_coe.mp hp)
    obtain ⟨N, hN, rfl⟩ := mem_gens.mp (Finset.mem_coe.mp hq)
    simp only [mono_mul]
    exact mono_mem ((card_union_le M N).trans (Nat.add_le_add hM hN))
  exact hle (Submodule.mul_mem_mul hf hg)

/-- In characteristic 2, `2^j = [j = 0]`. -/
lemma two_pow_zmod (j : ℕ) : ((2 : ZMod 2) ^ j) = if j = 0 then 1 else 0 := by
  rcases j with _ | j
  · simp
  · rw [pow_succ, show (2 : ZMod 2) = 0 from rfl, mul_zero]; simp

/-- Möbius interpolation on the lower part of the cube. -/
lemma interp_low (D : ℕ) (f : (Fin F → Bool) → ZMod 2) :
    ∃ g ∈ V (F := F) D, ∀ β, (ones β).card ≤ D → g β = f β := by
  classical
  set a : Finset (Fin F) → ZMod 2 := fun M => ∑ N ∈ M.powerset, f (ind N)
  refine ⟨∑ M ∈ univ.filter (fun M : Finset (Fin F) => M.card ≤ D), a M • mono M, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun M hM => Submodule.smul_mem _ _
      (mono_mem (by simpa using hM)))
  · intro β hβ
    set O := ones β
    have hind : ind O = β := by
      funext i; simp [ind, O, ones]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mono_eq]
    -- only `M ⊆ O` contribute, and all of them have `|M| ≤ D`
    have h1 : ∑ M ∈ univ.filter (fun M : Finset (Fin F) => M.card ≤ D),
        a M * (if M ⊆ O then 1 else 0) = ∑ M ∈ O.powerset, a M := by
      rw [← sum_filter_add_sum_filter_not (univ.filter (fun M : Finset (Fin F) => M.card ≤ D))
        (fun M => M ⊆ O)]
      rw [sum_eq_zero (s := (univ.filter (fun M : Finset (Fin F) => M.card ≤ D)).filter
        (fun M => ¬ M ⊆ O)) (fun M hM => by
          simp only [mem_filter] at hM; simp [hM.2]), add_zero]
      apply sum_congr
      · ext M
        simp only [mem_filter, mem_univ, true_and, mem_powerset]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨(card_le_card h).trans hβ, h⟩
      · intro M hM
        rw [if_pos (mem_powerset.mp hM), mul_one]
    rw [h1]
    -- swap the double sum
    have h2 : ∑ M ∈ O.powerset, a M
        = ∑ N ∈ O.powerset, ((Finset.Icc N O).card : ZMod 2) * f (ind N) := by
      simp only [a]
      rw [Finset.sum_comm' (t' := O.powerset) (s' := fun N => Finset.Icc N O)]
      · refine sum_congr rfl (fun N _ => ?_)
        rw [sum_const, nsmul_eq_mul]
      · intro M N
        simp only [mem_powerset, Finset.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h2.trans h1⟩
        · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h2, h1⟩
    rw [h2]
    rw [sum_eq_single O]
    · rw [Finset.Icc_self, card_singleton, Nat.cast_one, one_mul, hind]
    · intro N hN hNO
      rw [mem_powerset] at hN
      rw [Finset.card_Icc_finset hN, Nat.cast_pow, Nat.cast_ofNat, two_pow_zmod]
      have : O.card - N.card ≠ 0 := by
        have := card_lt_card (ssubset_of_subset_of_ne hN hNO)
        omega
      simp [this]
    · intro h; exact absurd (mem_powerset.mpr (subset_refl O)) h

/-- Complementing the cube. -/
def neg (β : Fin F → Bool) : Fin F → Bool := fun i => !β i

lemma mono_neg (M : Finset (Fin F)) :
    (fun β => mono M (neg β)) = ∑ N ∈ M.powerset, mono N := by
  classical
  funext β
  rw [Finset.sum_apply]
  simp only [mono_eq]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hc : (M.powerset.filter (fun N => N ⊆ ones β)) = (M ∩ ones β).powerset := by
    ext N; rw [mem_filter, mem_powerset, mem_powerset, subset_inter_iff]
  rw [hc, card_powerset, Nat.cast_pow, Nat.cast_ofNat, two_pow_zmod]
  have k1 : ∀ i, i ∈ ones (neg β) ↔ β i = false := by intro i; simp [ones, neg]
  have k2 : ∀ i, i ∈ ones β ↔ β i = true := by intro i; simp [ones]
  have : M ⊆ ones (neg β) ↔ (M ∩ ones β).card = 0 := by
    rw [card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    constructor
    · intro h i hi
      rw [mem_inter, k2] at hi
      have := (k1 i).mp (h hi.1)
      rw [this] at hi; exact Bool.false_ne_true hi.2
    · intro h i hi
      rw [k1]
      cases hb : β i
      · rfl
      · exact absurd (mem_inter.mpr ⟨hi, (k2 i).mpr hb⟩) (h i)
  by_cases h : M ⊆ ones (neg β)
  · rw [if_pos h, if_pos (this.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

lemma neg_mem {D : ℕ} {g : (Fin F → Bool) → ZMod 2} (hg : g ∈ V D) :
    (fun β => g (neg β)) ∈ V D := by
  classical
  let φ : ((Fin F → Bool) → ZMod 2) →ₗ[ZMod 2] ((Fin F → Bool) → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (neg (F := F))
  have hle : V (F := F) D ≤ (V D).comap φ := by
    unfold V
    apply Submodule.span_le.mpr
    intro f hf
    obtain ⟨M, hM, rfl⟩ := mem_gens.mp (Finset.mem_coe.mp hf)
    show φ (mono M) ∈ V D
    have : φ (mono M) = fun β => mono M (neg β) := rfl
    rw [this, mono_neg]
    exact Submodule.sum_mem _ (fun N hN =>
      mono_mem ((card_le_card (mem_powerset.mp hN)).trans hM))
  exact hle hg

lemma ones_neg_card (β : Fin F → Bool) : (ones (neg β)).card = F - (ones β).card := by
  classical
  have h : ones (neg β) = (ones β)ᶜ := by
    ext i; simp [ones, neg]
  rw [h, Finset.card_compl, Fintype.card_fin]

/-- The majority function at the exact median `⌈F/2⌉ = F - ⌊F/2⌋`. -/
def TH (β : Fin F → Bool) : ZMod 2 := if F - F / 2 ≤ (ones β).card then 1 else 0

/-- Every function is `g₀ + TH·(g₀ + g₁)` with `deg gᵢ ≤ ⌊F/2⌋`. -/
lemma decomp (f : (Fin F → Bool) → ZMod 2) :
    ∃ g₀ ∈ V (F := F) (F / 2), ∃ g₁ ∈ V (F := F) (F / 2),
      ∀ β, f β = g₀ β + TH β * (g₀ β + g₁ β) := by
  obtain ⟨g₀, hg₀, h₀⟩ := interp_low (F / 2) f
  obtain ⟨h, hh, h₁⟩ := interp_low (F / 2) (fun β => f (neg β))
  refine ⟨g₀, hg₀, fun β => h (neg β), neg_mem hh, fun β => ?_⟩
  have hnn : neg (neg β) = β := by funext i; simp [neg]
  unfold TH
  split_ifs with hT
  · have hc : (ones (neg β)).card ≤ F / 2 := by
      rw [ones_neg_card]; omega
    have := h₁ (neg β) hc
    simp only [hnn] at this
    show f β = g₀ β + 1 * (g₀ β + h (neg β))
    rw [this, one_mul, ← add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul,
      zero_add]
  · rw [zero_mul, add_zero, h₀ β (by omega)]

/-- **Smolensky's lemma at the median.** A function of degree `≤ d` agrees with `TH` on at most
`#{M : |M| ≤ ⌊F/2⌋ + d}` points. -/
theorem smolensky {d : ℕ} {Q : (Fin F → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    (univ.filter (fun β : Fin F → Bool => Q β = TH β)).card
      ≤ (univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2 + d)).card := by
  classical
  set S := univ.filter (fun β : Fin F → Bool => Q β = TH β)
  set D := F / 2 + d
  -- restriction to `S`
  let R : V (F := F) D →ₗ[ZMod 2] (S → ZMod 2) :=
    { toFun := fun g β => (g : (Fin F → Bool) → ZMod 2) β
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective R := by
    intro φ
    let f : (Fin F → Bool) → ZMod 2 := fun β => if h : β ∈ S then φ ⟨β, h⟩ else 0
    obtain ⟨g₀, hg₀, g₁, hg₁, hdec⟩ := decomp f
    have hmem : (fun β => g₀ β + Q β * (g₀ β + g₁ β)) ∈ V (F := F) D := by
      have h1 : g₀ ∈ V (F := F) D := V_mono (by omega) hg₀
      have h2 : Q * (g₀ + g₁) ∈ V (F := F) D := by
        have := mul_mem hQ (Submodule.add_mem _ hg₀ hg₁)
        rw [show D = d + F / 2 by omega]; exact this
      exact Submodule.add_mem _ h1 h2
    refine ⟨⟨_, hmem⟩, ?_⟩
    funext ⟨β, hβ⟩
    show g₀ β + Q β * (g₀ β + g₁ β) = φ ⟨β, hβ⟩
    have hQT : Q β = TH β := (mem_filter.mp hβ).2
    rw [hQT, ← hdec β]
    simp [f, hβ]
  have h1 : Module.finrank (ZMod 2) (S → ZMod 2) ≤ Module.finrank (ZMod 2) (V (F := F) D) := by
    have := LinearMap.finrank_range_le R
    rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at this
  have h2 : Module.finrank (ZMod 2) (V (F := F) D) ≤ (gens (F := F) D).card :=
    finrank_span_finset_le_card (R := ZMod 2) (gens (F := F) D)
  have h3 : (gens (F := F) D).card
      ≤ (univ.filter (fun M : Finset (Fin F) => M.card ≤ D)).card := card_image_le
  have h4 : Module.finrank (ZMod 2) (S → ZMod 2) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  omega

/-- Threshold at an arbitrary position `θ`. -/
def THg (θ : ℕ) (β : Fin F → Bool) : ZMod 2 := if θ ≤ (ones β).card then 1 else 0

/-- Every function is `g₀ + TH_θ·(g₀ + g₁)` with `deg gᵢ ≤ max(θ-1, F-θ)`. -/
lemma decomp_gen (θ : ℕ) (f : (Fin F → Bool) → ZMod 2) :
    ∃ g₀ ∈ V (F := F) (max (θ - 1) (F - θ)), ∃ g₁ ∈ V (F := F) (max (θ - 1) (F - θ)),
      ∀ β, f β = g₀ β + THg θ β * (g₀ β + g₁ β) := by
  set E := max (θ - 1) (F - θ)
  obtain ⟨g₀, hg₀, h₀⟩ := interp_low E f
  obtain ⟨h, hh, h₁⟩ := interp_low E (fun β => f (neg β))
  refine ⟨g₀, hg₀, fun β => h (neg β), neg_mem hh, fun β => ?_⟩
  have hnn : neg (neg β) = β := by funext i; simp [neg]
  have hle : (ones β).card ≤ F := by
    calc (ones β).card ≤ (univ : Finset (Fin F)).card := card_le_card (subset_univ _)
      _ = F := by simp
  unfold THg
  split_ifs with hT
  · have hc : (ones (neg β)).card ≤ E := by
      rw [ones_neg_card]; omega
    have := h₁ (neg β) hc
    simp only [hnn] at this
    show f β = g₀ β + 1 * (g₀ β + h (neg β))
    rw [this, one_mul, ← add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul,
      zero_add]
  · rw [zero_mul, add_zero, h₀ β (by omega)]

/-- **Smolensky's lemma at an arbitrary threshold.** A function of degree `≤ d` agrees with
`TH_θ` on at most `#{M : |M| ≤ max(θ-1, F-θ) + d}` points. -/
theorem smolensky_gen (θ : ℕ) {d : ℕ} {Q : (Fin F → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    (univ.filter (fun β : Fin F → Bool => Q β = THg θ β)).card
      ≤ (univ.filter (fun M : Finset (Fin F) => M.card ≤ max (θ - 1) (F - θ) + d)).card := by
  classical
  set S := univ.filter (fun β : Fin F → Bool => Q β = THg θ β)
  set D := max (θ - 1) (F - θ) + d
  let R : V (F := F) D →ₗ[ZMod 2] (S → ZMod 2) :=
    { toFun := fun g β => (g : (Fin F → Bool) → ZMod 2) β
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective R := by
    intro φ
    let f : (Fin F → Bool) → ZMod 2 := fun β => if h : β ∈ S then φ ⟨β, h⟩ else 0
    obtain ⟨g₀, hg₀, g₁, hg₁, hdec⟩ := decomp_gen θ f
    have hmem : (fun β => g₀ β + Q β * (g₀ β + g₁ β)) ∈ V (F := F) D := by
      have h1 : g₀ ∈ V (F := F) D := V_mono (by omega) hg₀
      have h2 : Q * (g₀ + g₁) ∈ V (F := F) D := by
        have := mul_mem hQ (Submodule.add_mem _ hg₀ hg₁)
        rw [show D = d + max (θ - 1) (F - θ) by omega]; exact this
      exact Submodule.add_mem _ h1 h2
    refine ⟨⟨_, hmem⟩, ?_⟩
    funext ⟨β, hβ⟩
    show g₀ β + Q β * (g₀ β + g₁ β) = φ ⟨β, hβ⟩
    have hQT : Q β = THg θ β := (mem_filter.mp hβ).2
    rw [hQT, ← hdec β]
    simp [f, hβ]
  have h1 : Module.finrank (ZMod 2) (S → ZMod 2) ≤ Module.finrank (ZMod 2) (V (F := F) D) := by
    have := LinearMap.finrank_range_le R
    rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at this
  have h2 : Module.finrank (ZMod 2) (V (F := F) D) ≤ (gens (F := F) D).card :=
    finrank_span_finset_le_card (R := ZMod 2) (gens (F := F) D)
  have h3 : (gens (F := F) D).card
      ≤ (univ.filter (fun M : Finset (Fin F) => M.card ≤ D)).card := card_image_le
  have h4 : Module.finrank (ZMod 2) (S → ZMod 2) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  omega

/-- Complemented threshold: `Q` agrees with `1 + TH_θ` iff `Q + 1` agrees with `TH_θ`. -/
theorem smolensky_gen_compl (θ : ℕ) {d : ℕ} {Q : (Fin F → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    (univ.filter (fun β : Fin F → Bool => Q β = 1 + THg θ β)).card
      ≤ (univ.filter (fun M : Finset (Fin F) => M.card ≤ max (θ - 1) (F - θ) + d)).card := by
  have hQ1 : (Q + 1) ∈ V (F := F) d := by
    refine Submodule.add_mem _ hQ ?_
    have : (1 : (Fin F → Bool) → ZMod 2) = mono ∅ := by
      funext β; simp [mono]
    rw [this]; exact mono_mem (by simp)
  refine le_trans (le_of_eq ?_) (smolensky_gen θ hQ1)
  congr 1
  ext β
  simp only [mem_filter, mem_univ, true_and, Pi.add_apply, Pi.one_apply]
  generalize Q β = a
  generalize THg θ β = b
  revert a b
  decide

end Smolensky

end ProblemQ
