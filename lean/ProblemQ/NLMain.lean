import ProblemQ.NLMarginal

/-!
# Theorem NL-U (kernel-checked)

**Model.** `m` i.i.d. uniform gates `(w, t) ∈ {0,1}^n × [-rad, rad]` in the `{0,1}`-input model.

**Template.** An oblivious list of `L` entries `P a : literals → gates → Fin (m+1) → F₂`, each output
of F₂-degree `≤ d` in the gate variables (any dependence on the literals).

**Success on `I`.** At least half of the columns of `I` have an entry that outputs `1hotSUM` of the
gates correctly at all but a `δ` fraction of the column's points.

**Theorem.** With `16 M² ≤ s`, `M s ≤ k`, `F₀ ≤ m π₀/2` for `π₀ = (3/5)/(2 rad + 1)`, `δ M ≤ 1/100`,
`n - k ≥ 400` and `20 q ≤ n - k`:

  #{ω : some `I` with `|I| = k` succeeds}
    ≤ C(n,k) · (50/3) · (M e^{-mπ₀/16} + C(n,q) (L (½ + (d+1)/√F₀)^M)^q) · |Gate|^m.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ}

/-- Disjoint blocks of size `s` inside any `I` with `M s ≤ |I|`. -/
lemma exists_blocks (s : ℕ) : ∀ (M : ℕ) (I : Finset (Fin n)), M * s ≤ I.card →
    ∃ A : Fin M → Finset (Fin n), (∀ i, A i ⊆ I) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧ ∀ i, (A i).card = s := by
  intro M
  induction M with
  | zero => intro I _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ M ih =>
    intro I hI
    obtain ⟨B, hBI, hB⟩ := exists_subset_card_eq (show s ≤ I.card by nlinarith)
    have hrest : M * s ≤ (I \ B).card := by
      rw [card_sdiff_of_subset hBI, hB]; rw [Nat.succ_mul] at hI; omega
    obtain ⟨A', hA'I, hA'd, hA'c⟩ := ih (I \ B) hrest
    refine ⟨Fin.cases B A', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hBI
      · simp only [Fin.cases_succ]; exact (hA'I j).trans sdiff_subset
    · intro i i'
      have hdB : ∀ j, Disjoint B (A' j) := fun j =>
        Finset.disjoint_of_subset_right (hA'I j) disjoint_sdiff
      refine Fin.cases ?_ (fun j => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) i' <;>
        intro hii'
      · exact absurd rfl hii'
      · simpa using hdB j'
      · simpa using (hdB j).symm
      · simp only [Fin.cases_succ]
        exact hA'd j j' (fun h => hii' (by rw [h]))
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hB
      · simpa using hA'c j

variable {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)

/-- The private-gate density used in the theorem. -/
def π₀ (n : ℕ) : ℝ := (3 / 5) / (2 * (rad n : ℝ) + 1)

lemma π₀_nonneg (n : ℕ) : 0 ≤ π₀ n := by
  unfold π₀; have : (0 : ℝ) < rad n := by unfold rad; positivity
  positivity

/-- Density hypothesis for `card_goodRows_le`. -/
lemma hπ_of_blocks {I : Finset (Fin n)} {x₀ : Fin n → Bool} {M s : ℕ}
    {A : Fin M → Finset (Fin n)} (hA : ∀ i, A i ⊆ I)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) (hcard : ∀ i, (A i).card = s)
    (hMs : 16 * M ^ 2 ≤ s) (i : Fin M) :
    π₀ n * Fintype.card (Rest (rows I x₀))
      ≤ ((univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i)).card : ℝ) := by
  have h1 := card_priv_ge (x₀ := x₀) hA hdisj hcard i
  have h2 := bonf_small (M := M) hMs
  have hcR : (Fintype.card (Rest (rows I x₀)) : ℝ)
      = (2 : ℝ) ^ Fintype.card {l // l ∉ rows I x₀} * (2 * (rad n : ℝ) + 1) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]
    push_cast
    rw [card_Tset]
  rw [hcR]
  have hr : (0 : ℝ) < 2 * (rad n : ℝ) + 1 := by
    have : (0 : ℝ) < rad n := by unfold rad; positivity
    linarith
  have e : π₀ n * ((2 : ℝ) ^ Fintype.card {l // l ∉ rows I x₀} * (2 * (rad n : ℝ) + 1))
      = 3 / 5 * (2 : ℝ) ^ Fintype.card {l // l ∉ rows I x₀} := by
    unfold π₀; field_simp
  rw [e]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card {l // l ∉ rows I x₀} := by positivity
  nlinarith

open Classical in
/-- **Per live set.** -/
theorem card_succeeds_le {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    (I : Finset (Fin n)) {M s q : ℕ} {δ : ℝ}
    (hMs : 16 * M ^ 2 ≤ s) (hsk : M * s ≤ I.card)
    (hF : (F₀ : ℝ) ≤ m * π₀ n / 2) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100)
    (hn' : 400 ≤ n - I.card) (hq : 20 * q ≤ n - I.card) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) => Succeeds P δ ω I)).card : ℝ)
      ≤ 50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
          (n.choose q : ℝ) * (L * p₀ ^ M) ^ q) *
          (Fintype.card (Gate n (Tset n)) : ℝ) ^ m) := by
  obtain ⟨A, hA, hdisj, hcard⟩ := exists_blocks s M I hsk
  set G : ℝ := (Fintype.card (Gate n (Tset n)) : ℝ) ^ m
  set B : ℝ := M * Real.exp (-(m * π₀ n / 16)) +
    (n.choose q : ℝ) * (L * p₀ ^ M) ^ q
  set S := univ.filter (fun ω : Fin m → Gate n (Tset n) => Succeeds P δ ω I)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  -- each base point
  have hx : ∀ x₀ : Fin n → Bool,
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) => q ≤ goodRows P I x₀ A ω)).card : ℝ)
        ≤ G * B := by
    intro x₀
    have h := card_goodRows_le (x₀ := x₀) P hA hP hp₀ (π₀_nonneg n)
      (fun i => hπ_of_blocks (x₀ := x₀) hA hdisj hcard hMs i) hF q
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hc : ((rows I x₀).card.choose q : ℝ) ≤ n.choose q := by
      have : (rows I x₀).card ≤ n := (card_le_univ _).trans (by simp)
      exact_mod_cast Nat.choose_le_choose q this
    have : 0 ≤ (L * p₀ ^ M) ^ q := pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)) _
    simp only [B]
    nlinarith
  -- double counting
  have hdc : ∑ ω ∈ S, ((univ.filter (fun x₀ : Fin n → Bool =>
      q ≤ goodRows P I x₀ A ω)).card : ℝ)
        ≤ ∑ x₀ : Fin n → Bool, ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          q ≤ goodRows P I x₀ A ω)).card : ℝ) := by
    calc ∑ ω ∈ S, ((univ.filter (fun x₀ : Fin n → Bool =>
          q ≤ goodRows P I x₀ A ω)).card : ℝ)
        ≤ ∑ ω : Fin m → Gate n (Tset n), ((univ.filter (fun x₀ : Fin n → Bool =>
          q ≤ goodRows P I x₀ A ω)).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      _ = _ := by
          simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
          exact sum_comm
  have hlow : (S.card : ℝ) * (3 / 50 * 2 ^ n)
      ≤ ∑ ω ∈ S, ((univ.filter (fun x₀ : Fin n → Bool =>
          q ≤ goodRows P I x₀ A ω)).card : ℝ) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum (fun ω hω => ?_)
    simp only [S, mem_filter, mem_univ, true_and] at hω
    exact many_good_frames P δ ω hA hω hδ0 hδM hn' q hq
  have hup : ∑ x₀ : Fin n → Bool, ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
      q ≤ goodRows P I x₀ A ω)).card : ℝ) ≤ 2 ^ n * (G * B) := by
    calc _ ≤ ∑ _x₀ : Fin n → Bool, G * B := sum_le_sum (fun x₀ _ => hx x₀)
      _ = 2 ^ n * (G * B) := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            nsmul_eq_mul]; push_cast; ring
  have := hlow.trans (hdc.trans hup)
  have hfin : (S.card : ℝ) * (3 / 50) ≤ G * B := by
    have h' : (S.card : ℝ) * (3 / 50) * 2 ^ n ≤ G * B * 2 ^ n := by nlinarith
    exact le_of_mul_le_mul_right h' h2n
  calc (S.card : ℝ) ≤ 50 / 3 * (G * B) := by linarith
    _ = 50 / 3 * (B * G) := by ring

open Classical in
/-- **Theorem NL-U, generic form** (union over all live sets of size `k`): any correctness
notion with a per-point bound `p₀` on `≥ F₀` private coins. -/
theorem nl_gen {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    {k M s q : ℕ} {δ : ℝ}
    (hMs : 16 * M ^ 2 ≤ s) (hsk : M * s ≤ k)
    (hF : (F₀ : ℝ) ≤ m * π₀ n / 2) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100)
    (hn' : 400 ≤ n - k) (hq : 20 * q ≤ n - k) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds P δ ω I)).card : ℝ)
      ≤ (n.choose k : ℝ) * (50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
          (n.choose q : ℝ) * (L * p₀ ^ M) ^ q) *
          (Fintype.card (Gate n (Tset n)) : ℝ) ^ m)) := by
  have hsub : univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds P δ ω I)
      ⊆ (univ.powersetCard k).biUnion (fun I => univ.filter
          (fun ω : Fin m → Gate n (Tset n) => Succeeds P δ ω I)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    obtain ⟨I, hI, hS⟩ := hω
    exact mem_biUnion.mpr ⟨I, mem_powersetCard.mpr ⟨subset_univ _, hI⟩, by simpa using hS⟩
  calc ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds P δ ω I)).card : ℝ)
      ≤ ∑ I ∈ (univ : Finset (Fin n)).powersetCard k, ((univ.filter
          (fun ω : Fin m → Gate n (Tset n) => Succeeds P δ ω I)).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_le.mpr ((card_le_card hsub).trans card_biUnion_le)
    _ ≤ ∑ _I ∈ (univ : Finset (Fin n)).powersetCard k, 50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
          (n.choose q : ℝ) * (L * p₀ ^ M) ^ q) *
          (Fintype.card (Gate n (Tset n)) : ℝ) ^ m) := by
        refine sum_le_sum (fun I hI => ?_)
        have hIk : I.card = k := (mem_powersetCard.mp hI).2
        exact card_succeeds_le P hP hp₀ I hMs (hIk ▸ hsk) hF hδ0 hδM (hIk ▸ hn') (hIk ▸ hq)
    _ = _ := by rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Instance: `1hotSUM` (Theorem NL-U as stated in the notes) -/

/-- Correctness of a `1hotSUM` entry, as a Boolean. -/
def hotP {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2) :
    Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool :=
  fun a y u => decide (Smolensky.Correct (P a y) u)

/-- Smolensky at the median gives the per-point bound `½ + (d+1)/√F₀`. -/
lemma pointBound_hot {m L d : ℕ}
    (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d) {F₀ : ℕ} (hF₀ : 1 ≤ F₀) :
    PointBound (hotP P) F₀ (1 / 2 + (d + 1) / Real.sqrt F₀) := by
  intro a y Pset u₀ hcard
  have hF : 1 ≤ Pset.card := le_trans hF₀ hcard
  have hpt := Smolensky.point_bound hF (P a y) (hP a y) Pset Pset.equivFin.symm u₀
  have h2F : (0 : ℝ) < 2 ^ Pset.card := by positivity
  rw [div_le_iff₀ h2F] at hpt
  simp only [hotP, decide_eq_true_eq]
  refine le_trans hpt ?_
  apply mul_le_mul_of_nonneg_right _ h2F.le
  have hsq : Real.sqrt F₀ ≤ Real.sqrt Pset.card := Real.sqrt_le_sqrt (by exact_mod_cast hcard)
  have hsq0 : 0 < Real.sqrt F₀ := Real.sqrt_pos.mpr (by exact_mod_cast hF₀)
  have : (d + 1 : ℝ) / Real.sqrt Pset.card ≤ (d + 1) / Real.sqrt F₀ :=
    div_le_div_of_nonneg_left (by positivity) hsq0 hsq
  linarith

open Classical in
/-- **Theorem NL-U** (union over all live sets of size `k`). -/
theorem nl_u {m L d : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2)
    (hP : ∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d)
    {k M s q F₀ : ℕ} {δ : ℝ}
    (hMs : 16 * M ^ 2 ≤ s) (hsk : M * s ≤ k) (hF₀ : 1 ≤ F₀)
    (hF : (F₀ : ℝ) ≤ m * π₀ n / 2) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100)
    (hn' : 400 ≤ n - k) (hq : 20 * q ≤ n - k) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (hotP P) δ ω I)).card : ℝ)
      ≤ (n.choose k : ℝ) * (50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
          (n.choose q : ℝ) * (L * (1 / 2 + (d + 1) / Real.sqrt F₀) ^ M) ^ q) *
          (Fintype.card (Gate n (Tset n)) : ℝ) ^ m)) :=
  nl_gen (hotP P) (pointBound_hot P hP hF₀) (by positivity) hMs hsk hF hδ0 hδM hn' hq

end NLU

end

end ProblemQ
