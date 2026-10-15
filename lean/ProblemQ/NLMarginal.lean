import ProblemQ.NLTypical

/-!
# Theorem NL-U, part 6: from "the list succeeds on `I`" to many good frames

If at least half of the columns of `I` have an entry correct at all but a `δ` fraction of their
points, then for at least a `3/50` fraction of base points `x₀`, the frame has `≥ q` good rows
(`20 q ≤ n - |I|`, `δ M ≤ 1/100`, `n - |I| ≥ 400`). Rows are counted through the bijection
`(x₀, o) ↦ (x₀ + e_o, o)`; incorrect frame points through the injection `(x₀, o) ↦ (rpt o i, o)`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n m L : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool)
  (δ : ℝ) (ω : Fin m → Gate n (Tset n)) (I : Finset (Fin n))

/-- Projection to the outside coordinates (inside set to `0`). -/
def proj (x : Fin n → Bool) : Fin n → Bool := fun l => if l ∈ I then false else x l

/-- A column (given by any of its points) has an entry correct at all but a `δ` fraction. -/
def colGood (z : Fin n → Bool) : Prop :=
  ∃ a, ((univ.filter (fun y : I → Bool =>
    ¬ P a (merge I z y) (gvec ω (merge I z y)) = true)).card : ℝ) ≤ δ * 2 ^ I.card

open Classical in
/-- The list succeeds on `I`: at least half of the columns are good. -/
def Succeeds : Prop := (2 : ℝ) ^ n / 2 ≤ ((univ.filter (fun z => colGood P δ ω I z)).card : ℝ)

variable {I}

lemma merge_proj (x : Fin n → Bool) (y : I → Bool) : merge I (proj I x) y = merge I x y := by
  funext l; unfold merge proj; by_cases h : l ∈ I <;> simp [h]

lemma colGood_proj (x : Fin n → Bool) : colGood P δ ω I (proj I x) ↔ colGood P δ ω I x := by
  unfold colGood; simp only [merge_proj]

lemma proj_eq {x x' : Fin n → Bool} (h : ∀ l, l ∉ I → x l = x' l) : proj I x = proj I x' := by
  funext l; unfold proj; by_cases hl : l ∈ I <;> simp [hl, h]

lemma merge_self (x : Fin n → Bool) :
    merge I (proj I x) (fun j => x j) = x := by
  funext l; unfold merge proj; by_cases h : l ∈ I <;> simp [h]

/-- Bad points: in a good column, but the column's chosen entry is wrong there. -/
def badAt (x : Fin n → Bool) : Prop :=
  ∃ h : colGood P δ ω I (proj I x),
    ¬ P (Classical.choose h) x (gvec ω x) = true

open Classical in
/-- At most a `δ` fraction of all points are bad. -/
theorem card_bad_le (I : Finset (Fin n)) (hδ : 0 ≤ δ) :
    ((univ.filter (fun x : Fin n → Bool => badAt (I := I) P δ ω x)).card : ℝ) ≤ δ * 2 ^ n := by
  -- split `x` into (inside, outside)
  have hsplit : (univ.filter (fun x : Fin n → Bool => badAt (I := I) P δ ω x)).card
      = ∑ u : {l // l ∉ I} → Bool, (univ.filter (fun y : I → Bool =>
          badAt (I := I) P δ ω ((Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm
            (y, u)))).card := by
    rw [← Finset.card_sigma]
    refine card_bij (fun x _ => ⟨fun l => x l, fun l => x l⟩) ?_ ?_ ?_
    · intro x hx
      simp only [mem_sigma, mem_univ, mem_filter, true_and] at hx ⊢
      have : (Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm
          (fun l => x l, fun l => x l) = x := by
        funext l; by_cases h : l ∈ I <;> simp [Equiv.piEquivPiSubtypeProd, h]
      rw [this]; exact hx
    · intro x _ x' _ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      funext l
      by_cases hl : l ∈ I
      · have := congrFun (eq_of_heq h2) ⟨l, hl⟩; simpa using this
      · have := congrFun h1 ⟨l, hl⟩; simpa using this
    · rintro ⟨u, y⟩ hb
      simp only [mem_sigma, mem_univ, mem_filter, true_and] at hb
      refine ⟨_, by simpa using hb, ?_⟩
      simp only [Sigma.mk.injEq]
      constructor
      · funext l; simp [Equiv.piEquivPiSubtypeProd, l.2]
      · apply heq_of_eq; funext l; simp [Equiv.piEquivPiSubtypeProd, l.2]
  have hper : ∀ u : {l // l ∉ I} → Bool, ((univ.filter (fun y : I → Bool =>
      badAt (I := I) P δ ω ((Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm
        (y, u)))).card : ℝ) ≤ δ * 2 ^ I.card := by
    intro u
    set z : Fin n → Bool := fun l => if h : l ∈ I then false else u ⟨l, h⟩
    have hx : ∀ y : I → Bool,
        (Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm (y, u)
          = merge I z y := by
      intro y; funext l; by_cases h : l ∈ I <;> simp [Equiv.piEquivPiSubtypeProd, merge, z, h]
    have hp : ∀ y : I → Bool, proj I (merge I z y) = z := by
      intro y; funext l; by_cases h : l ∈ I <;> simp [proj, merge, z, h]
    by_cases hg : colGood P δ ω I z
    · have hspec := Classical.choose_spec hg
      refine le_trans ?_ hspec
      refine Nat.cast_le.mpr (card_le_card (fun y hy => ?_))
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      rw [hx] at hy
      obtain ⟨h, hh⟩ := hy
      have key : ∀ (z' : Fin n → Bool) (hz : z' = z) (h' : colGood P δ ω I z'),
          Classical.choose h' = Classical.choose hg := by
        intro z' hz h'; subst hz; rfl
      have : Classical.choose h = Classical.choose hg := key _ (hp y) h
      rw [this] at hh; exact hh
    · have : univ.filter (fun y : I → Bool =>
          badAt (I := I) P δ ω ((Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm
            (y, u))) = ∅ := by
        rw [filter_eq_empty_iff]
        intro y _ hy
        rw [hx] at hy
        obtain ⟨h, _⟩ := hy
        rw [hp] at h
        exact hg h
      rw [this]; simp; positivity
  rw [hsplit, Nat.cast_sum]
  calc ∑ u : {l // l ∉ I} → Bool, ((univ.filter (fun y : I → Bool =>
        badAt (I := I) P δ ω ((Equiv.piEquivPiSubtypeProd (fun l => l ∈ I) (fun _ => Bool)).symm
          (y, u)))).card : ℝ)
      ≤ ∑ _u : {l // l ∉ I} → Bool, δ * 2 ^ I.card := sum_le_sum (fun u _ => hper u)
    _ = δ * 2 ^ n := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
          Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
        push_cast
        have hI : I.card ≤ n := by
          have := card_le_univ I; rwa [Fintype.card_fin] at this
        rw [mul_comm, mul_assoc, ← pow_add, Nat.add_sub_cancel' hI]

section Frames

variable {M : ℕ} {A : Fin M → Finset (Fin n)}

lemma proj_rpt (hA : ∀ i, A i ⊆ I) (x₀ : Fin n → Bool) (o : Fin n) (i : Fin M) :
    proj I (rpt x₀ A o i) = proj I (Function.update x₀ o true) := by
  apply proj_eq
  intro l hl
  unfold rpt bpt
  by_cases ho : l = o
  · subst ho; simp
  · rw [Function.update_of_ne ho, Function.update_of_ne ho]
    have : l ∉ A i := fun h => hl (hA i h)
    simp [this]

/-- Sum of signs over the outside coordinates is `2·#ones - n'`. -/
lemma sum_sg_out (x : Fin n → Bool) :
    ∑ l ∈ univ.filter (fun l => l ∉ I), sg (x l)
      = 2 * ((univ.filter (fun l => l ∉ I ∧ x l = true)).card : ℤ)
        - (univ.filter (fun l : Fin n => l ∉ I)).card := by
  have : ∀ l, sg (x l) = 2 * (if x l = true then 1 else 0) - 1 := by
    intro l; cases x l <;> simp [sg]
  simp_rw [this]
  rw [sum_sub_distrib, ← mul_sum, sum_boole, sum_const, nsmul_eq_mul, mul_one, filter_filter]

lemma card_out (I : Finset (Fin n)) :
    (univ.filter (fun l : Fin n => l ∉ I)).card = n - I.card := by
  rw [filter_not, card_sdiff, card_univ, Fintype.card_fin]
  simp [filter_mem_eq_inter, univ_inter]

/-- Chebyshev: few points have fewer than `n'/4` outside ones. -/
lemma card_few_ones (hn' : 1 ≤ n - I.card) :
    ((univ.filter (fun x : Fin n → Bool =>
        4 * (univ.filter (fun l => l ∉ I ∧ x l = true)).card < n - I.card)).card : ℝ)
      ≤ 4 * 2 ^ n / (n - I.card : ℕ) := by
  classical
  set n' := n - I.card
  set B := univ.filter (fun l : Fin n => l ∉ I)
  have hB : B.card = n' := card_out I
  have hsq := sum_sq_signs (α := Fin n) B
  rw [hB, Fintype.card_fin] at hsq
  have hn'r : (0 : ℝ) < n' := by exact_mod_cast hn'
  set bad := univ.filter (fun x : Fin n → Bool =>
    4 * (univ.filter (fun l => l ∉ I ∧ x l = true)).card < n')
  have h1 : (bad.card : ℝ) * ((n' : ℝ) / 2) ^ 2
      ≤ ∑ x : Fin n → Bool, ((∑ l ∈ B, sg (x l) : ℤ) : ℝ) ^ 2 := by
    calc (bad.card : ℝ) * ((n' : ℝ) / 2) ^ 2 = ∑ x ∈ bad, ((n' : ℝ) / 2) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ bad, ((∑ l ∈ B, sg (x l) : ℤ) : ℝ) ^ 2 := by
          refine sum_le_sum (fun x hx => ?_)
          simp only [bad, mem_filter, mem_univ, true_and] at hx
          have hs := sum_sg_out (I := I) x
          rw [card_out] at hs
          have : ((∑ l ∈ B, sg (x l) : ℤ) : ℝ) < -((n' : ℝ) / 2) := by
            have hz : (∑ l ∈ B, sg (x l) : ℤ) * 2 < -(n' : ℤ) := by
              rw [hs]; push_cast; omega
            have : ((∑ l ∈ B, sg (x l) : ℤ) : ℝ) * 2 < -(n' : ℝ) := by exact_mod_cast hz
            linarith
          nlinarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h2 : ∑ x : Fin n → Bool, ((∑ l ∈ B, sg (x l) : ℤ) : ℝ) ^ 2 = n' * 2 ^ n := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hsq; push_cast at this ⊢; exact this
  rw [h2] at h1
  rw [le_div_iff₀ hn'r]
  nlinarith

open Classical in
/-- **Many good frames.** -/
theorem many_good_frames (hA : ∀ i, A i ⊆ I) (hS : Succeeds P δ ω I) (hδ0 : 0 ≤ δ)
    (hδM : δ * M ≤ 1 / 100) (hn' : 400 ≤ n - I.card) (q : ℕ) (hq : 20 * q ≤ n - I.card) :
    (3 / 50 : ℝ) * 2 ^ n
      ≤ ((univ.filter (fun x₀ : Fin n → Bool => q ≤ goodRows P I x₀ A ω)).card : ℝ) := by
  set n' := n - I.card
  have hn'r : (400 : ℝ) ≤ n' := by exact_mod_cast hn'
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  set GP := univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2 ∉ I ∧ p.1 p.2 = false ∧ colGood P δ ω I (proj I (Function.update p.1 p.2 true)) ∧
      ∀ i, ¬ badAt (I := I) P δ ω (rpt p.1 A p.2 i))
  set g : (Fin n → Bool) → ℕ := fun x₀ =>
    (univ.filter (fun o : Fin n => (x₀, o) ∈ GP)).card
  -- (1) good pairs give good rows
  have hg : ∀ x₀, g x₀ ≤ goodRows P I x₀ A ω := by
    intro x₀
    have hmem : ∀ o, (x₀, o) ∈ GP → o ∈ rows I x₀ := by
      intro o ho
      simp only [GP, mem_filter, mem_univ, true_and] at ho
      simp [rows, ho.1, ho.2.1]
    have heq : g x₀ = (univ.filter (fun o : {o // o ∈ rows I x₀} => (x₀, o.1) ∈ GP)).card := by
      refine card_bij (fun o ho => ⟨o, hmem o (by simpa using ho)⟩) ?_ ?_ ?_
      · intro o ho; simpa using ho
      · intro a _ b _ h; simpa using h
      · intro o ho; exact ⟨o.1, by simpa using ho, rfl⟩
    rw [heq]
    unfold goodRows
    apply card_le_card
    intro o ho
    simp only [mem_filter, mem_univ, true_and, GP] at ho ⊢
    obtain ⟨_, _, hc, hb⟩ := ho
    refine ⟨Classical.choose hc, fun i => ?_⟩
    have hbi := hb i
    unfold badAt at hbi
    push Not at hbi
    have hp : proj I (rpt x₀ A o i) = proj I (Function.update x₀ o true) := proj_rpt hA x₀ o i
    have hc' : colGood P δ ω I (proj I (rpt x₀ A o i)) := by rw [hp]; exact hc
    have key : ∀ (z' : Fin n → Bool) (hz : z' = proj I (Function.update x₀ o true))
        (h' : colGood P δ ω I z'), Classical.choose h' = Classical.choose hc := by
      intro z' hz h'; subst hz; rfl
    have := hbi hc'
    rwa [key _ hp hc'] at this
  -- (2) counting pairs
  have hcardGP : (GP.card : ℝ) = ∑ x₀ : Fin n → Bool, (g x₀ : ℝ) := by
    simp only [g]
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl (fun x₀ _ => ?_)
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun o _ => ?_)
    simp only [GP, mem_filter, mem_univ, true_and]
  set A1 := univ.filter (fun p : (Fin n → Bool) × Fin n =>
    p.2 ∉ I ∧ p.1 p.2 = false ∧ colGood P δ ω I (proj I (Function.update p.1 p.2 true)))
  set Bi : Fin M → Finset ((Fin n → Bool) × Fin n) := fun i => univ.filter
    (fun p : (Fin n → Bool) × Fin n =>
      p.2 ∉ I ∧ p.1 p.2 = false ∧ badAt (I := I) P δ ω (rpt p.1 A p.2 i))
  have hA1 : A1 ⊆ GP ∪ univ.biUnion Bi := by
    intro p hp
    simp only [A1, mem_filter, mem_univ, true_and] at hp
    by_cases h : ∀ i, ¬ badAt (I := I) P δ ω (rpt p.1 A p.2 i)
    · exact mem_union_left _ (by simp [GP, hp.1, hp.2.1, hp.2.2, h])
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, by simp [Bi, hp.1, hp.2.1, hi]⟩)
  -- (3) A1 is large
  set good := univ.filter (fun x : Fin n → Bool => colGood P δ ω I (proj I x))
  set few := univ.filter (fun x : Fin n → Bool =>
    4 * (univ.filter (fun l => l ∉ I ∧ x l = true)).card < n')
  have hgood : (2 : ℝ) ^ n / 2 ≤ good.card := by
    have : good = univ.filter (fun z => colGood P δ ω I z) := by
      ext x; simp only [good, mem_filter, mem_univ, true_and, colGood_proj]
    rw [this]; exact hS
  have hfew := card_few_ones (I := I) (by omega)
  have hA1card : (n' : ℝ) / 4 * (good.card - few.card) ≤ A1.card := by
    -- bijection with (x, o), x o = true
    have hbij : A1.card = (univ.filter (fun p : (Fin n → Bool) × Fin n =>
        p.2 ∉ I ∧ p.1 p.2 = true ∧ colGood P δ ω I (proj I p.1))).card := by
      refine card_bij (fun p _ => (Function.update p.1 p.2 true, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [A1, mem_filter, mem_univ, true_and] at hp ⊢
        exact ⟨hp.1, by simp, hp.2.2⟩
      · intro p hp p' hp' h
        simp only [A1, mem_filter, mem_univ, true_and] at hp hp'
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        refine Prod.ext ?_ h2
        funext l
        by_cases hl : l = p.2
        · subst hl; rw [hp.2.1, h2, hp'.2.1]
        · have := congrFun h1 l
          rw [Function.update_of_ne hl] at this
          rw [Function.update_of_ne (by rw [← h2]; exact hl)] at this
          exact this
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp
        have hself : Function.update p.1 p.2 true = p.1 := by
          rw [← hp.2.1]; exact Function.update_eq_self _ _
        refine ⟨(Function.update p.1 p.2 false, p.2), ?_, ?_⟩
        · simp only [A1, mem_filter, mem_univ, true_and]
          refine ⟨hp.1, by simp, ?_⟩
          rw [Function.update_idem, hself]; exact hp.2.2
        · refine Prod.ext ?_ rfl
          show Function.update (Function.update p.1 p.2 false) p.2 true = p.1
          rw [Function.update_idem, hself]
    rw [hbij]
    have hsum : ((univ.filter (fun p : (Fin n → Bool) × Fin n =>
        p.2 ∉ I ∧ p.1 p.2 = true ∧ colGood P δ ω I (proj I p.1))).card : ℝ)
        = ∑ x ∈ good, ((univ.filter (fun l => l ∉ I ∧ x l = true)).card : ℝ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type]
      rw [← sum_filter_add_sum_filter_not univ (fun x => colGood P δ ω I (proj I x))]
      rw [sum_eq_zero (s := univ.filter (fun x => ¬ colGood P δ ω I (proj I x)))
        (fun x hx => by
          simp only [mem_filter, mem_univ, true_and] at hx
          exact sum_eq_zero (fun o _ => by simp [hx])), add_zero]
      refine sum_congr rfl (fun x hx => ?_)
      simp only [good, mem_filter, mem_univ, true_and] at hx
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      refine sum_congr rfl (fun o _ => ?_)
      simp [hx]
    rw [hsum]
    calc (n' : ℝ) / 4 * (good.card - few.card) ≤ (n' : ℝ) / 4 * ((good \ few).card : ℝ) := by
          have : (good.card : ℝ) - few.card ≤ (good \ few).card := by
            have := card_sdiff_add_card_inter good few
            have h2 := card_le_card (inter_subset_right (s₁ := good) (s₂ := few))
            have : ((good \ few).card : ℝ) + (good ∩ few).card = good.card := by
              exact_mod_cast this
            have h3 : ((good ∩ few).card : ℝ) ≤ few.card := by exact_mod_cast h2
            linarith
          gcongr
      _ = ∑ x ∈ good \ few, (n' : ℝ) / 4 := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ good \ few, ((univ.filter (fun l => l ∉ I ∧ x l = true)).card : ℝ) := by
          refine sum_le_sum (fun x hx => ?_)
          simp only [few, mem_sdiff, mem_filter, mem_univ, true_and, not_lt] at hx
          have : (n' : ℝ) ≤ 4 * (univ.filter (fun l => l ∉ I ∧ x l = true)).card := by
            exact_mod_cast hx.2
          linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
  -- (4) each B_i is small
  have hbad := card_bad_le P δ ω I hδ0
  have hBi : ∀ i, ((Bi i).card : ℝ) ≤ n' * (δ * 2 ^ n) := by
    intro i
    have hinj : (Bi i).card ≤ ((univ.filter (fun x : Fin n → Bool =>
        badAt (I := I) P δ ω x)) ×ˢ (univ.filter (fun l : Fin n => l ∉ I))).card := by
      refine card_le_card_of_injOn (fun p => (rpt p.1 A p.2 i, p.2)) ?_ ?_
      · intro p hp
        simp only [Bi, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
        simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod,
          Set.mem_setOf_eq]
        exact ⟨hp.2.2, hp.1⟩
      · intro p hp p' hp' h
        simp only [Bi, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        refine Prod.ext ?_ h2
        funext l
        by_cases hl : l = p.2
        · subst hl; rw [hp.2.1, h2, hp'.2.1]
        · have := congrFun h1 l
          unfold rpt bpt at this
          rw [Function.update_of_ne hl] at this
          rw [Function.update_of_ne (by rw [← h2]; exact hl)] at this
          by_cases hlA : l ∈ A i
          · simp only [hlA, if_true] at this; exact Bool.not_inj this
          · simpa [hlA] using this
    rw [card_product, card_out] at hinj
    have : ((Bi i).card : ℝ) ≤ ((univ.filter (fun x : Fin n → Bool =>
        badAt (I := I) P δ ω x)).card : ℝ) * n' := by exact_mod_cast hinj
    nlinarith [Nat.cast_nonneg (α := ℝ) n']
  -- (5) assemble a lower bound on #GP
  have hGP : (n' : ℝ) / 4 * (2 ^ n / 2 - 4 * 2 ^ n / n') - M * (n' * (δ * 2 ^ n)) ≤ GP.card := by
    have h1 : (A1.card : ℝ) ≤ GP.card + ∑ i : Fin M, ((Bi i).card : ℝ) := by
      have := (card_le_card hA1).trans ((card_union_le _ _).trans
        (Nat.add_le_add_left card_biUnion_le _))
      rw [← Nat.cast_sum]; exact_mod_cast this
    have h2 : ∑ i : Fin M, ((Bi i).card : ℝ) ≤ M * (n' * (δ * 2 ^ n)) := by
      calc ∑ i : Fin M, ((Bi i).card : ℝ) ≤ ∑ _i : Fin M, (n' : ℝ) * (δ * 2 ^ n) :=
            sum_le_sum (fun i _ => hBi i)
        _ = M * (n' * (δ * 2 ^ n)) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (n' : ℝ) / 4 * (2 ^ n / 2 - 4 * 2 ^ n / n') ≤ (n' : ℝ) / 4 * (good.card - few.card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hfew, hgood]
    linarith
  -- (6) reverse Markov
  have hgle : ∀ x₀, (g x₀ : ℝ) ≤ n' := by
    intro x₀
    have : g x₀ ≤ n' := by
      show g x₀ ≤ n - I.card
      rw [← card_out I]
      apply card_le_card
      intro o ho
      simp only [mem_filter, mem_univ, true_and, GP] at ho ⊢
      exact ho.1
    exact_mod_cast this
  set Nq := univ.filter (fun x₀ : Fin n → Bool => q ≤ g x₀)
  have hmarkov : ∑ x₀ : Fin n → Bool, (g x₀ : ℝ) ≤ Nq.card * n' + 2 ^ n * q := by
    rw [← sum_filter_add_sum_filter_not univ (fun x₀ => q ≤ g x₀)]
    have e1 : ∑ x₀ ∈ Nq, (g x₀ : ℝ) ≤ Nq.card * n' := by
      calc ∑ x₀ ∈ Nq, (g x₀ : ℝ) ≤ ∑ _x₀ ∈ Nq, (n' : ℝ) := sum_le_sum (fun x₀ _ => hgle x₀)
        _ = Nq.card * n' := by rw [sum_const, nsmul_eq_mul]
    have e2 : ∑ x₀ ∈ univ.filter (fun x₀ => ¬ q ≤ g x₀), (g x₀ : ℝ) ≤ 2 ^ n * q := by
      calc ∑ x₀ ∈ univ.filter (fun x₀ => ¬ q ≤ g x₀), (g x₀ : ℝ)
          ≤ ∑ _x₀ ∈ univ.filter (fun x₀ : Fin n → Bool => ¬ q ≤ g x₀), (q : ℝ) := by
            refine sum_le_sum (fun x₀ hx => ?_)
            simp only [mem_filter, mem_univ, true_and, not_le] at hx
            exact_mod_cast hx.le
        _ ≤ ∑ _x₀ : Fin n → Bool, (q : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
        _ = 2 ^ n * q := by
            rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
              nsmul_eq_mul]; push_cast; ring
    linarith
  have hNq : (Nq.card : ℝ) ≤ ((univ.filter (fun x₀ : Fin n → Bool =>
      q ≤ goodRows P I x₀ A ω)).card : ℝ) := by
    exact_mod_cast card_le_card (fun x₀ hx => by
      simp only [Nq, mem_filter, mem_univ, true_and] at hx ⊢; exact hx.trans (hg x₀))
  -- arithmetic
  have hqr : (q : ℝ) * 20 ≤ n' := by exact_mod_cast (by omega : q * 20 ≤ n')
  have hMδ : (M : ℝ) * δ ≤ 1 / 100 := by linarith [mul_comm δ (M : ℝ)]
  have hfin : (3 / 50 : ℝ) * 2 ^ n * n' ≤ Nq.card * n' := by
    have e : (n' : ℝ) / 4 * (2 ^ n / 2 - 4 * 2 ^ n / n') = 2 ^ n * (n' / 8 - 1) := by
      field_simp; ring
    rw [e] at hGP
    have : (M : ℝ) * (n' * (δ * 2 ^ n)) = (M * δ) * (n' * 2 ^ n) := by ring
    rw [this] at hGP
    have hMδ' : (M * δ) * ((n' : ℝ) * 2 ^ n) ≤ 1 / 100 * (n' * 2 ^ n) :=
      mul_le_mul_of_nonneg_right hMδ (by positivity)
    nlinarith
  have hn'pos : (0 : ℝ) < n' := by linarith
  have := le_of_mul_le_mul_right hfin hn'pos
  linarith

end Frames

end NLU

end

end ProblemQ
