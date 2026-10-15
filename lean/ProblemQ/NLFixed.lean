import ProblemQ.NLFrame

/-!
# Theorem NL-U, part 4: the bound for a fixed base point

For fixed `I`, `x₀`, blocks `A`: the number of circuits with at least `q` good rows is at most
`|Gate|^m · (M e^{-mπ/16} + C(|O|, q) (L p₀^M)^q)`, provided every block's private-gate density
is `≥ π` and `F₀ ≤ mπ/2`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ} {I : Finset (Fin n)} {x₀ : Fin n → Bool} {M : ℕ} {A : Fin M → Finset (Fin n)}

section Decomp

variable (O : Finset (Fin n)) {m : ℕ}

/-- Circuit = (row coin vectors, rests). -/
def circEquiv : (Fin m → Gate n (Tset n)) ≃ (({l // l ∈ O}) → Fin m → Bool) × (Fin m → Rest O) where
  toFun ω := (fun o j => (gateEquiv O (ω j)).1 o, fun j => (gateEquiv O (ω j)).2)
  invFun p := fun j => (gateEquiv O).symm (fun o => p.1 o j, p.2 j)
  left_inv ω := by funext j; simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext o j; simp
    · funext j; simp

end Decomp

/-- Number of good rows of a circuit. -/
def goodRows {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)
    (I : Finset (Fin n)) (x₀ : Fin n → Bool) (A : Fin M → Finset (Fin n))
    (ω : Fin m → Gate n (Tset n)) : ℕ :=
  (univ.filter (fun o : {o // o ∈ rows I x₀} =>
    ∃ a, ∀ i, P a (rpt x₀ A o i) (gvec ω (rpt x₀ A o i)) = true)).card

lemma gvec_rpt_eq {m : ℕ} (hA : ∀ i, A i ⊆ I) (ω : Fin m → Gate n (Tset n))
    (o : {o // o ∈ rows I x₀}) (i : Fin M) :
    gvec ω (rpt x₀ A o i)
      = rvec x₀ A (circEquiv (rows I x₀) ω).2 ((circEquiv (rows I x₀) ω).1 o) i := by
  funext j
  unfold gvec rvec
  rw [gval_rpt_eq hA rfl o.2 i]
  rfl

section Atypical

variable {O : Finset (Fin n)} {m : ℕ}

/-- **Typicality via Chernoff.** -/
theorem card_atypical_le (i : Fin M) {π : ℝ} (hπ0 : 0 ≤ π)
    (hπ : π * Fintype.card (Rest O)
      ≤ ((univ.filter (fun r : Rest O => privR (x₀ := x₀) (A := A) r i)).card : ℝ))
    {F₀ : ℕ} (hF : (F₀ : ℝ) ≤ m * π / 2) :
    ((univ.filter (fun ρ : Fin m → Rest O =>
        (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)).card : ℝ)
      ≤ (Fintype.card (Rest O) : ℝ) ^ m * Real.exp (-(m * π / 16)) := by
  classical
  set C : ℝ := (Fintype.card (Rest O) : ℝ)
  have hC : 0 < C := by
    have : 0 < Fintype.card (Rest O) := Fintype.card_pos
    simp only [C]; exact_mod_cast this
  set ind : Rest O → ℝ := fun r => if privR (x₀ := x₀) (A := A) r i then 1 else 0
  set μ : ℝ := (∑ r, ind r) / C
  have hsum : ∑ r, ind r = ((univ.filter (fun r : Rest O =>
      privR (x₀ := x₀) (A := A) r i)).card : ℝ) := by
    simp [ind, sum_ite]
  have hμπ : π ≤ μ := by
    simp only [μ]; rw [le_div_iff₀ hC, hsum]; linarith
  have hμ0 : 0 ≤ μ := le_trans hπ0 hμπ
  set g : Rest O → ℝ := fun r => -ind r
  have hg : ∀ r, |g r| ≤ 1 := by
    intro r; simp only [g, ind]; split_ifs <;> simp
  have ha : ∑ r, g r ≤ C * (-μ) := by
    simp only [g, sum_neg_distrib, μ]; rw [mul_neg, mul_div_cancel₀ _ hC.ne']
  have hb : ∑ r, g r ^ 2 ≤ C * μ := by
    have : ∀ r, g r ^ 2 = ind r := by
      intro r; simp only [g, ind]; split_ifs <;> norm_num
    simp only [this, μ]; rw [mul_div_cancel₀ _ hC.ne']
  have htail := card_tail_le (m := m) g hg (lam := 1 / 4) (by norm_num) (by norm_num) ha hb
    (-(F₀ : ℝ))
  have hsub : univ.filter (fun ρ : Fin m → Rest O => (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)
      ⊆ tail (m := m) g (-(F₀ : ℝ)) := by
    intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ
    simp only [tail, mem_filter, mem_univ, true_and]
    have hcard : ((Priv (x₀ := x₀) (A := A) ρ i).card : ℝ) = ∑ j, ind (ρ j) := by
      simp [Priv, ind, sum_ite]
    have : (∑ j, ind (ρ j)) ≤ F₀ := by
      rw [← hcard]; exact_mod_cast hρ.le
    simp only [g, sum_neg_distrib]
    linarith
  calc ((univ.filter (fun ρ : Fin m → Rest O =>
        (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)).card : ℝ)
      ≤ ((tail (m := m) g (-(F₀ : ℝ))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ C ^ m * Real.exp (m * (1 / 4 * -μ + (1 / 4) ^ 2 * μ) - 1 / 4 * -(F₀ : ℝ)) := htail
    _ ≤ C ^ m * Real.exp (-(m * π / 16)) := by
        gcongr
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith [mul_le_mul_of_nonneg_left hμπ hm0]

end Atypical

section Fixed

variable {m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)

/-- **Fixed base point.** -/
theorem card_goodRows_le (hA : ∀ i, A i ⊆ I)
    {F₀ : ℕ} {p₀ : ℝ} (hP : PointBound P F₀ p₀) (hp₀ : 0 ≤ p₀)
    {π : ℝ} (hπ0 : 0 ≤ π)
    (hπ : ∀ i, π * Fintype.card (Rest (rows I x₀))
      ≤ ((univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i)).card : ℝ))
    (hF : (F₀ : ℝ) ≤ m * π / 2) (q : ℕ) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) => q ≤ goodRows P I x₀ A ω)).card : ℝ)
      ≤ (Fintype.card (Gate n (Tset n)) : ℝ) ^ m *
        (M * Real.exp (-(m * π / 16)) +
          ((rows I x₀).card.choose q : ℝ) *
            (L * p₀ ^ M) ^ q) := by
  classical
  set O := rows I x₀
  set p : ℝ := L * p₀ ^ M
  have hp0 : 0 ≤ p := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)
  set CR : ℝ := (Fintype.card (Rest O) : ℝ)
  set CW : ℝ := (2 : ℝ) ^ m
  -- |Gate|^m = CW^|O| · CR^m
  have hG : (Fintype.card (Gate n (Tset n)) : ℝ) ^ m = CW ^ O.card * CR ^ m := by
    rw [Fintype.card_congr (gateEquiv O), Fintype.card_prod, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_coe]
    simp only [CW, CR]
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
  -- transport to (W, ρ)
  have htr : (univ.filter (fun ω : Fin m → Gate n (Tset n) => q ≤ goodRows P I x₀ A ω)).card
      = (univ.filter (fun p : ({l // l ∈ O} → Fin m → Bool) × (Fin m → Rest O) =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P p.2 o (p.1 o))).card)).card := by
    refine card_bij (fun ω _ => circEquiv O ω) ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      unfold goodRows at hω
      simp only [gvec_rpt_eq hA] at hω
      exact hω
    · intro ω _ ω' _ h; exact (circEquiv O).injective h
    · intro p hp
      refine ⟨(circEquiv O).symm p, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      unfold goodRows
      simp only [gvec_rpt_eq hA]
      rw [show circEquiv (rows I x₀) ((circEquiv O).symm p) = p from
        (circEquiv O).apply_symm_apply p]
      exact hp
  rw [htr]
  -- sum over ρ
  have hsplit : ((univ.filter (fun p : ({l // l ∈ O} → Fin m → Bool) × (Fin m → Rest O) =>
        q ≤ (univ.filter (fun o : {o // o ∈ O} =>
          rowGood (x₀ := x₀) (A := A) P p.2 o (p.1 o))).card)).card : ℝ)
      = ∑ ρ : Fin m → Rest O, ((univ.filter (fun W : {l // l ∈ O} → Fin m → Bool =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P ρ o (W o))).card)).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl (fun ρ _ => ?_)
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [hsplit]
  -- typical ρ: independent rows; atypical ρ: trivial bound
  set Atyp := univ.filter (fun ρ : Fin m → Rest O =>
    ∃ i, (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)
  have hper : ∀ ρ : Fin m → Rest O,
      ((univ.filter (fun W : {l // l ∈ O} → Fin m → Bool =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P ρ o (W o))).card)).card : ℝ)
        ≤ (if ρ ∈ Atyp then CW ^ O.card else 0)
          + (O.card.choose q : ℝ) * p ^ q * CW ^ O.card := by
    intro ρ
    by_cases hρ : ρ ∈ Atyp
    · rw [if_pos hρ]
      have : ((univ.filter (fun W : {l // l ∈ O} → Fin m → Bool =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P ρ o (W o))).card)).card : ℝ) ≤ CW ^ O.card := by
        have h1 := card_le_univ (univ.filter (fun W : {l // l ∈ O} → Fin m → Bool =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P ρ o (W o))).card))
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          Fintype.card_coe] at h1
        simp only [CW]; exact_mod_cast h1
      have : 0 ≤ (O.card.choose q : ℝ) * p ^ q * CW ^ O.card :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (by positivity)
      linarith
    · rw [if_neg hρ, zero_add]
      have htyp : ∀ i, F₀ ≤ (Priv (x₀ := x₀) (A := A) ρ i).card := by
        intro i; by_contra h; push Not at h
        exact hρ (by simp only [Atyp, mem_filter, mem_univ, true_and]; exact ⟨i, h⟩)
      have h := card_many_idx (ι := {o // o ∈ O}) (Γ := Fin m → Bool) q
        (fun o => univ.filter (fun u => rowGood (x₀ := x₀) (A := A) P ρ o u)) hp0
        (fun o => by
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          push_cast
          exact row_good_le P hP hp₀ ρ o htyp)
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_coe] at h
      simp only [mem_filter, mem_univ, true_and] at h
      push_cast at h
      exact h
  calc ∑ ρ : Fin m → Rest O, ((univ.filter (fun W : {l // l ∈ O} → Fin m → Bool =>
          q ≤ (univ.filter (fun o : {o // o ∈ O} =>
            rowGood (x₀ := x₀) (A := A) P ρ o (W o))).card)).card : ℝ)
      ≤ ∑ ρ : Fin m → Rest O, ((if ρ ∈ Atyp then CW ^ O.card else 0)
          + (O.card.choose q : ℝ) * p ^ q * CW ^ O.card) := sum_le_sum (fun ρ _ => hper ρ)
    _ = (Atyp.card : ℝ) * CW ^ O.card
          + CR ^ m * ((O.card.choose q : ℝ) * p ^ q * CW ^ O.card) := by
        rw [sum_add_distrib, sum_ite_mem, univ_inter, sum_const, sum_const, card_univ,
          Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        simp only [CR]; push_cast; ring
    _ ≤ (M * (CR ^ m * Real.exp (-(m * π / 16)))) * CW ^ O.card
          + CR ^ m * ((O.card.choose q : ℝ) * p ^ q * CW ^ O.card) := by
        gcongr
        -- union over blocks
        have hsub : Atyp ⊆ univ.biUnion (fun i : Fin M => univ.filter
            (fun ρ : Fin m → Rest O => (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)) := by
          intro ρ hρ
          simp only [Atyp, mem_filter, mem_univ, true_and] at hρ
          obtain ⟨i, hi⟩ := hρ
          exact mem_biUnion.mpr ⟨i, mem_univ i, by simpa using hi⟩
        calc (Atyp.card : ℝ)
            ≤ ∑ i : Fin M, ((univ.filter (fun ρ : Fin m → Rest O =>
                (Priv (x₀ := x₀) (A := A) ρ i).card < F₀)).card : ℝ) := by
              rw [← Nat.cast_sum]
              exact Nat.cast_le.mpr ((card_le_card hsub).trans card_biUnion_le)
          _ ≤ ∑ _i : Fin M, CR ^ m * Real.exp (-(m * π / 16)) :=
              sum_le_sum (fun i _ => card_atypical_le i hπ0 (hπ i) hF)
          _ = M * (CR ^ m * Real.exp (-(m * π / 16))) := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Fintype.card (Gate n (Tset n)) : ℝ) ^ m *
          (M * Real.exp (-(m * π / 16)) + (O.card.choose q : ℝ) * p ^ q) := by
        rw [hG]; ring

end Fixed

end NLU

end

end ProblemQ
