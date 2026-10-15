import ProblemQ.NLRow

/-!
# Theorem NL-U, part 3: the coin decomposition for a fixed base point

A gate splits as (row weights `w|_O`, rest `(w|_{Oᶜ}, t)`). At row point `rpt o i` its value is
`rvec ρ u i j`, where `ρ` collects the rests of all gates and `u j = w_j(o)` is row `o`'s coin
vector. Given `ρ`, the rows are independent; inside a row the private blocks are independent.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ} (O : Finset (Fin n))

/-- Everything of a gate except its row weights. -/
abbrev Rest := ({l // l ∉ O} → Bool) × (Tset n)

/-- Gate = (row weights, rest). -/
def gateEquiv : Gate n (Tset n) ≃ ({l // l ∈ O} → Bool) × Rest O :=
  (Equiv.prodCongr (Equiv.piEquivPiSubtypeProd (fun l => l ∈ O) (fun _ => Bool))
    (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

variable {O} (x₀ : Fin n → Bool) {M : ℕ} (A : Fin M → Finset (Fin n))

/-- Sum at block point `i`, read off the rest. -/
def linR (r : Rest O) (i : Fin M) : ℤ :=
  ∑ l : {l // l ∉ O}, if bpt x₀ A i l then sg (r.1 l) else 0

/-- Sensitivity at block `i`, read off the rest. -/
def sensR (r : Rest O) (i : Fin M) : Prop :=
  0 ≤ (r.2 : ℤ) - linR x₀ A r i ∧ (r.2 : ℤ) - linR x₀ A r i ≤ 1

instance (r : Rest O) (i : Fin M) : Decidable (sensR x₀ A r i) := by
  unfold sensR; infer_instance

/-- Constant value of an insensitive gate. -/
def constR (r : Rest O) (i : Fin M) : Bool := decide ((r.2 : ℤ) ≤ linR x₀ A r i - 1)

/-- Gate vector at the row points of block `i`, as a function of the row's coin vector `u`. -/
def rvec {m : ℕ} (ρ : Fin m → Rest O) (u : Fin m → Bool) (i : Fin M) : Fin m → Bool :=
  fun j => if sensR x₀ A (ρ j) i then u j else constR x₀ A (ρ j) i

variable {I : Finset (Fin n)} {x₀ A}

lemma lin_bpt_eq (hA : ∀ i, A i ⊆ I) (hO : O = rows I x₀) (γ : Gate n (Tset n)) (i : Fin M) :
    lin γ.1 (bpt x₀ A i) = linR x₀ A (gateEquiv O γ).2 i := by
  classical
  unfold lin linR
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun l => l ∈ O)
    (fun l => if bpt x₀ A i l then sg (γ.1 l) else 0)
  rw [← hsplit]
  have key : ∀ a b c : ℤ, a = 0 → b = c → a + b = c := by intros; subst_vars; simp
  apply key
  · refine Finset.sum_eq_zero (fun l _ => ?_)
    have hl : (l : Fin n) ∈ O := l.2
    have : bpt x₀ A i l = false := bpt_row hA (hO ▸ hl) i
    simp [this]
  · rfl

lemma gval_rpt_eq (hA : ∀ i, A i ⊆ I) (hO : O = rows I x₀) {o : Fin n} (ho : o ∈ O)
    (i : Fin M) (γ : Gate n (Tset n)) :
    gval γ (rpt x₀ A o i) =
      if sensR x₀ A (gateEquiv O γ).2 i then (gateEquiv O γ).1 ⟨o, ho⟩
      else constR x₀ A (gateEquiv O γ).2 i := by
  rw [gval_rpt hA (hO ▸ ho) i]
  have hs : sens (x₀ := x₀) (A := A) γ i ↔ sensR x₀ A (gateEquiv O γ).2 i := by
    unfold sens sensR; rw [lin_bpt_eq hA hO γ i]; rfl
  by_cases h : sens (x₀ := x₀) (A := A) γ i
  · rw [if_pos h, if_pos (hs.mp h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (hs.mpr h'))]
    unfold constR; rw [lin_bpt_eq hA hO γ i]; rfl

/-- Private gates of block `i`: sensitive at `i` and at no other block. -/
def privR (r : Rest O) (i : Fin M) : Prop := sensR x₀ A r i ∧ ∀ i', i' ≠ i → ¬ sensR x₀ A r i'

instance (r : Rest O) (i : Fin M) : Decidable (privR (x₀ := x₀) (A := A) r i) := by
  unfold privR; infer_instance

/-- Private block of `i` among the gates. -/
def Priv {m : ℕ} (ρ : Fin m → Rest O) (i : Fin M) : Finset (Fin m) :=
  univ.filter (fun j => privR (x₀ := x₀) (A := A) (ρ j) i)

lemma mem_Priv {m : ℕ} (ρ : Fin m → Rest O) (i : Fin M) (j : Fin m) :
    j ∈ Priv (x₀ := x₀) (A := A) ρ i ↔ privR (x₀ := x₀) (A := A) (ρ j) i := by
  simp [Priv]

section RowBound

variable {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)

/-- A row is good if some entry is correct at all its `M` points. -/
def rowGood (ρ : Fin m → Rest O) (o : Fin n) (u : Fin m → Bool) : Prop :=
  ∃ a, ∀ i, P a (rpt x₀ A o i) (rvec x₀ A ρ u i) = true

instance (ρ : Fin m → Rest O) (o : Fin n) (u : Fin m → Bool) :
    Decidable (rowGood (x₀ := x₀) (A := A) P ρ o u) := by
  unfold rowGood; infer_instance

/-- **Per-point bound (abstract).** If at least `F₀` gates (the set `Pset`) carry fair coins
and the other gates are fixed to `u₀`, every entry is correct at every point for at most a `p₀`
fraction of the coins. -/
def PointBound {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool) (F₀ : ℕ)
    (p₀ : ℝ) : Prop :=
  ∀ a y (Pset : Finset (Fin m)) (u₀ : Fin m → Bool), F₀ ≤ Pset.card →
    ((univ.filter (fun β : Fin Pset.card → Bool =>
      P a y (Smolensky.embed Pset Pset.equivFin.symm u₀ β) = true)).card : ℝ)
      ≤ p₀ * 2 ^ Pset.card

/-- One block: with the rest of the row fixed, the entry is correct at point `i` for at most a
`p₀` fraction of the block's coins. -/
lemma block_count {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀)
    (ρ : Fin m → Rest O) (o : Fin n) (a : Fin L) (i : Fin M) (Pset : Finset (Fin m))
    (hsens : ∀ j ∈ Pset, sensR x₀ A (ρ j) i) (γ : {j // j ∉ Pset} → Bool)
    (hcard : F₀ ≤ Pset.card) :
    ((univ.filter (fun β : {j // j ∈ Pset} → Bool =>
        P a (rpt x₀ A o i) (rvec x₀ A ρ (joinB Pset β γ) i) = true)).card : ℝ)
      ≤ p₀ * 2 ^ Pset.card := by
  classical
  set F := Pset.card
  set e : Fin F ≃ Pset := Pset.equivFin.symm
  set u₀ : Fin m → Bool := rvec x₀ A ρ (joinB Pset (fun _ => false) γ) i
  have hemb : ∀ β : {j // j ∈ Pset} → Bool,
      rvec x₀ A ρ (joinB Pset β γ) i = Smolensky.embed Pset e u₀ (fun k => β (e k)) := by
    intro β
    funext j
    unfold Smolensky.embed
    by_cases hj : j ∈ Pset
    · rw [dif_pos hj]
      simp only [rvec, hsens j hj, if_true]
      rw [joinB_in _ _ _ hj]
      simp
    · rw [dif_neg hj]
      simp only [u₀, rvec]
      split_ifs
      · rw [joinB_out _ _ _ hj, joinB_out _ _ _ hj]
      · rfl
  have hcount : (univ.filter (fun β : {j // j ∈ Pset} → Bool =>
      P a (rpt x₀ A o i) (rvec x₀ A ρ (joinB Pset β γ) i) = true)).card
      = (univ.filter (fun β' : Fin F → Bool =>
          P a (rpt x₀ A o i) (Smolensky.embed Pset e u₀ β') = true)).card := by
    refine card_bij (fun β _ => fun k => β (e k)) ?_ ?_ ?_
    · intro β hβ
      simp only [mem_filter, mem_univ, true_and] at hβ ⊢
      rwa [← hemb]
    · intro β _ β' _ h
      funext j
      have := congrFun h (e.symm j)
      simpa using this
    · intro β' hβ'
      refine ⟨fun j => β' (e.symm j), ?_, by funext k; simp⟩
      simp only [mem_filter, mem_univ, true_and] at hβ' ⊢
      rw [hemb]
      simpa using hβ'
  rw [hcount]
  exact hP a _ Pset u₀ hcard

/-- Inside a typical row, one entry is correct at all `M` points with density `≤ p₀^M`. -/
theorem row_entry_le {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    (ρ : Fin m → Rest O) (o : Fin n) (a : Fin L)
    (htyp : ∀ i, F₀ ≤ (Priv (x₀ := x₀) (A := A) ρ i).card) :
    ((univ.filter (fun u : Fin m → Bool =>
        ∀ i, P a (rpt x₀ A o i) (rvec x₀ A ρ u i) = true)).card : ℝ)
      ≤ p₀ ^ M * 2 ^ m := by
  classical
  apply card_forall_le (Pv := fun i => Priv (x₀ := x₀) (A := A) ρ i) _ hp₀
  · -- block `i'` is invisible to event `i`
    intro i i' hii' u u' hu
    have : rvec x₀ A ρ u i = rvec x₀ A ρ u' i := by
      funext j
      unfold rvec
      split_ifs with hs
      · apply hu
        intro hj
        have hj' : j ∈ Priv (x₀ := x₀) (A := A) ρ i' := hj
        exact ((mem_Priv ρ i' j).mp hj').2 i hii' hs
      · rfl
    rw [this]
  · intro i γ
    exact block_count P hP ρ o a i (Priv (x₀ := x₀) (A := A) ρ i)
      (fun j hj => ((mem_Priv ρ i j).mp hj).1) γ (htyp i)

/-- A typical row is good with density `≤ L p₀^M`. -/
theorem row_good_le {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    (ρ : Fin m → Rest O) (o : Fin n)
    (htyp : ∀ i, F₀ ≤ (Priv (x₀ := x₀) (A := A) ρ i).card) :
    ((univ.filter (fun u : Fin m → Bool => rowGood (x₀ := x₀) (A := A) P ρ o u)).card : ℝ)
      ≤ L * p₀ ^ M * 2 ^ m := by
  classical
  have hsub : univ.filter (fun u : Fin m → Bool => rowGood (x₀ := x₀) (A := A) P ρ o u)
      ⊆ univ.biUnion (fun a : Fin L => univ.filter (fun u : Fin m → Bool =>
          ∀ i, P a (rpt x₀ A o i) (rvec x₀ A ρ u i) = true)) := by
    intro u hu
    rw [mem_filter] at hu
    obtain ⟨a, ha⟩ := hu.2
    exact mem_biUnion.mpr ⟨a, mem_univ a, by simpa using ha⟩
  calc ((univ.filter (fun u : Fin m → Bool => rowGood (x₀ := x₀) (A := A) P ρ o u)).card : ℝ)
      ≤ ∑ a : Fin L, ((univ.filter (fun u : Fin m → Bool =>
          ∀ i, P a (rpt x₀ A o i) (rvec x₀ A ρ u i) = true)).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_le.mpr ((card_le_card hsub).trans card_biUnion_le)
    _ ≤ ∑ _a : Fin L, p₀ ^ M * 2 ^ m :=
        sum_le_sum (fun a _ => row_entry_le P hP hp₀ ρ o a htyp)
    _ = L * p₀ ^ M * 2 ^ m := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end RowBound

end NLU

end

end ProblemQ
