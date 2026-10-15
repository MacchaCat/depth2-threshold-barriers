import ProblemQ.NLFixed

/-!
# Theorem NL-U, part 5: the private-gate density `π` (Bonferroni)

For a uniformly random rest `r = (w, t)`:
* `Pr[sens_i] ≥ 1.5/(2·rad+1)`: `t` is uniform on `[-rad, rad]` and independent of `w`, and by
  Chebyshev `|c_i(w)| < rad` with probability `≥ 3/4`;
* `Pr[sens_i ∧ sens_{i'}] ≤ (2/(2·rad+1)) · 3·C(2s,s)/4^s`: both force `|c_i - c_{i'}| ≤ 1`, and
  `c_i - c_{i'}` is a signed sum of `2s` independent signs;
* hence `Pr[priv_i] ≥ (1.5 - 6(M-1)·C(2s,s)/4^s)/(2·rad+1)`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

section Signs

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma sg_not (b : Bool) : sg (!b) = - sg b := by cases b <;> simp [sg]

/-- Orthogonality of the sign coordinates. -/
lemma sum_sg_mul (l l' : α) :
    ∑ w : α → Bool, sg (w l) * sg (w l') = if l = l' then (2 : ℤ) ^ Fintype.card α else 0 := by
  classical
  split_ifs with h
  · subst h
    simp [sg_sq, Fintype.card_fun, Fintype.card_bool]
  · -- flipping coordinate `l` negates every term
    set φ : (α → Bool) ≃ (α → Bool) :=
      { toFun := fun w => Function.update w l (!w l)
        invFun := fun w => Function.update w l (!w l)
        left_inv := fun w => by funext x; by_cases hx : x = l <;> simp [Function.update, hx]
        right_inv := fun w => by funext x; by_cases hx : x = l <;> simp [Function.update, hx] }
    have hneg : ∑ w : α → Bool, sg (w l) * sg (w l')
        = - ∑ w : α → Bool, sg (w l) * sg (w l') := by
      conv_lhs => rw [← Equiv.sum_comp φ]
      rw [← sum_neg_distrib]
      refine sum_congr rfl (fun w _ => ?_)
      simp only [φ, Equiv.coe_fn_mk, Function.update_self,
        Function.update_of_ne (Ne.symm h), sg_not]
      ring
    linarith

/-- Second moment of a sum of signs over a set `B`. -/
lemma sum_sq_signs (B : Finset α) :
    ∑ w : α → Bool, (∑ l ∈ B, sg (w l)) ^ 2 = B.card * (2 : ℤ) ^ Fintype.card α := by
  classical
  simp_rw [sq, sum_mul_sum]
  rw [sum_comm]
  rw [sum_congr rfl (fun l _ => by rw [sum_comm])]
  simp_rw [sum_sg_mul]
  rw [sum_congr rfl (fun l hl => by rw [sum_ite_eq, if_pos hl])]
  rw [sum_const, nsmul_eq_mul]

/-- Point probabilities of a signed sum of signs are at most the central binomial weight. -/
lemma card_signsum_le (D : Finset α) (ε : α → Bool) (v : ℤ) :
    (univ.filter (fun w : α → Bool =>
        ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)) = v)).card
      ≤ D.card.choose (D.card / 2) * 2 ^ (Fintype.card α - D.card) := by
  classical
  -- remove the signs by flipping
  set φ : (α → Bool) ≃ (α → Bool) :=
    { toFun := fun w l => if ε l then w l else !w l
      invFun := fun w l => if ε l then w l else !w l
      left_inv := fun w => by funext l; by_cases h : ε l <;> simp [h]
      right_inv := fun w => by funext l; by_cases h : ε l <;> simp [h] }
  have hflip : ∀ w, ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l))
      = ∑ l ∈ D, sg (φ w l) := by
    intro w; refine sum_congr rfl (fun l _ => ?_)
    by_cases h : ε l <;> simp [φ, h, sg_not]
  have h1 : (univ.filter (fun w : α → Bool =>
        ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)) = v)).card
      = (univ.filter (fun w : α → Bool => ∑ l ∈ D, sg (w l) = v)).card := by
    refine card_bij (fun w _ => φ w) ?_ ?_ ?_
    · intro w hw; simp only [mem_filter, mem_univ, true_and] at hw ⊢; rwa [← hflip]
    · intro a _ b _ h; exact φ.injective h
    · intro w hw
      refine ⟨φ.symm w, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      rw [hflip]; simpa using hw
  rw [h1]
  -- the sum fixes the number of ones in `D`
  have hsum : ∀ w : α → Bool,
      ∑ l ∈ D, sg (w l) = 2 * ((D.filter (fun l => w l = true)).card : ℤ) - D.card := by
    intro w
    have : ∀ l, sg (w l) = 2 * (if w l = true then 1 else 0) - 1 := by
      intro l; cases w l <;> simp [sg]
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, sum_boole, sum_const, nsmul_eq_mul, mul_one]
  set j : ℕ := ((v + D.card) / 2).toNat
  have hsub : univ.filter (fun w : α → Bool => ∑ l ∈ D, sg (w l) = v)
      ⊆ univ.filter (fun w : α → Bool => (D.filter (fun l => w l = true)).card = j) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [hsum] at hw
    simp only [j]; omega
  refine (card_le_card hsub).trans ?_
  -- inject into (ones in `D`, values outside `D`)
  have hinj : (univ.filter (fun w : α → Bool => (D.filter (fun l => w l = true)).card = j)).card
      ≤ (D.powersetCard j ×ˢ (univ : Finset ({l // l ∉ D} → Bool))).card := by
    refine card_le_card_of_injOn (fun w => (D.filter (fun l => w l = true),
      fun l : {l // l ∉ D} => w l)) ?_ ?_
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
      simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard, filter_subset,
        true_and, coe_univ, Set.mem_univ, and_true]
      exact hw
    · intro w _ w' _ h
      simp only [Prod.mk.injEq] at h
      funext l
      by_cases hl : l ∈ D
      · have := congrArg (fun S => l ∈ S) h.1
        simp only [mem_filter, hl, true_and] at this
        cases hw : w l <;> cases hw' : w' l <;> simp_all
      · exact congrFun h.2 ⟨l, hl⟩
  refine hinj.trans ?_
  rw [card_product, card_powersetCard, card_univ, Fintype.card_fun, Fintype.card_bool]
  have hc : Fintype.card {l // l ∉ D} = Fintype.card α - D.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hc]
  exact Nat.mul_le_mul_right _ (Nat.choose_le_middle _ _)

end Signs

section Density

variable {n : ℕ} {I : Finset (Fin n)} {x₀ : Fin n → Bool} {M : ℕ} {A : Fin M → Finset (Fin n)}

local notation "Oc" => {l // l ∉ rows I x₀}

lemma card_Tset (n : ℕ) : (Fintype.card (Tset n) : ℝ) = 2 * (rad n : ℝ) + 1 := by
  rw [Fintype.card_coe]
  simp only [Tset, Int.card_Icc]
  have h0 : 0 ≤ rad n := by unfold rad; positivity
  have hx : (((rad n + 1 - -rad n).toNat : ℕ) : ℤ) = 2 * rad n + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have : (((rad n + 1 - -rad n).toNat : ℕ) : ℝ) = 2 * (rad n : ℝ) + 1 := by exact_mod_cast hx
  exact this

lemma rad_sq_ge (n : ℕ) : (4 : ℝ) * n ≤ (rad n : ℝ) ^ 2 := by
  have h1 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have h2 : (n : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) * ((Nat.sqrt n : ℝ) + 1) := by exact_mod_cast h1
    nlinarith
  unfold rad; push_cast; nlinarith

/-- The block sum as a sum of signs over `B_i`. -/
lemma linR_eq (r : Rest (rows I x₀)) (i : Fin M) :
    linR x₀ A r i = ∑ l ∈ univ.filter (fun l : Oc => bpt x₀ A i l = true), sg (r.1 l) := by
  unfold linR; rw [sum_filter]

/-- Number of thresholds hitting a window of width 2. -/
lemma card_t_le (c : ℤ) :
    (univ.filter (fun t : Tset n => 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c ≤ 1)).card ≤ 2 := by
  classical
  have hsub : (univ.filter (fun t : Tset n => 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c ≤ 1)).map
      (Function.Embedding.subtype _) ⊆ {c, c + 1} := by
    intro x hx
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simp only [mem_insert, mem_singleton]; omega
  have := card_le_card hsub
  rw [card_map] at this
  exact this.trans (card_insert_le _ _)

lemma card_t_ge (c : ℤ) (hc : |c| < rad n) :
    2 ≤ (univ.filter (fun t : Tset n => 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c ≤ 1)).card := by
  classical
  rw [abs_lt] at hc
  have h1 : c ∈ Tset n := by simp only [Tset, mem_Icc]; constructor <;> omega
  have h2 : c + 1 ∈ Tset n := by simp only [Tset, mem_Icc]; constructor <;> omega
  have hsub : ({⟨c, h1⟩, ⟨c + 1, h2⟩} : Finset (Tset n))
      ⊆ univ.filter (fun t : Tset n => 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c ≤ 1) := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    simp only [mem_filter, mem_univ, true_and]
    rcases ht with rfl | rfl <;> simp
  have hne : (⟨c, h1⟩ : Tset n) ≠ ⟨c + 1, h2⟩ := by
    intro h; have := congrArg Subtype.val h; simp at this
  calc 2 = ({⟨c, h1⟩, ⟨c + 1, h2⟩} : Finset (Tset n)).card := by
        rw [card_insert_of_notMem (by simpa using hne), card_singleton]
    _ ≤ _ := card_le_card hsub

/-- Splitting a count over `Rest` into weights and thresholds. -/
lemma card_rest_split (Φ : (Oc → Bool) → Tset n → Prop) [∀ w t, Decidable (Φ w t)] :
    ((univ.filter (fun r : Rest (rows I x₀) => Φ r.1 r.2)).card : ℝ)
      = ∑ w : Oc → Bool, ((univ.filter (fun t : Tset n => Φ w t)).card : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl (fun w _ => ?_)
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]

/-- **Single block.** `Pr[sens_i] ≥ 1.5/(2·rad+1)`. -/
theorem card_sens_ge (i : Fin M) :
    (3 / 2 : ℝ) * 2 ^ Fintype.card Oc
      ≤ ((univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i)).card : ℝ) := by
  classical
  set B := univ.filter (fun l : Oc => bpt x₀ A i l = true)
  set D : ℝ := (2 : ℝ) ^ Fintype.card Oc
  have hD : 0 < D := by positivity
  have hsplit := card_rest_split (I := I) (x₀ := x₀)
    (fun w t => 0 ≤ (t : ℤ) - ∑ l ∈ B, sg (w l) ∧ (t : ℤ) - ∑ l ∈ B, sg (w l) ≤ 1)
  have heq : univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i)
      = univ.filter (fun r : Rest (rows I x₀) =>
          0 ≤ (r.2 : ℤ) - ∑ l ∈ B, sg (r.1 l) ∧ (r.2 : ℤ) - ∑ l ∈ B, sg (r.1 l) ≤ 1) := by
    ext r; simp only [mem_filter, mem_univ, true_and]; unfold sensR; rw [linR_eq]
  rw [heq, hsplit]
  -- Chebyshev: few weights have a large block sum
  set bad := univ.filter (fun w : Oc → Bool => rad n ≤ |∑ l ∈ B, sg (w l)|)
  have hcheb : (bad.card : ℝ) ≤ D / 4 := by
    have hsq := sum_sq_signs (α := Oc) B
    have hB : (B.card : ℝ) ≤ n := by
      have : B.card ≤ n := (card_le_univ B).trans (by
        rw [Fintype.card_subtype_compl, Fintype.card_fin]; omega)
      exact_mod_cast this
    have hr := rad_sq_ge n
    have hrpos : (0 : ℝ) < rad n := by unfold rad; positivity
    have h1 : (bad.card : ℝ) * (rad n : ℝ) ^ 2
        ≤ ∑ w : Oc → Bool, ((∑ l ∈ B, sg (w l) : ℤ) : ℝ) ^ 2 := by
      calc (bad.card : ℝ) * (rad n : ℝ) ^ 2 = ∑ w ∈ bad, (rad n : ℝ) ^ 2 := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ w ∈ bad, ((∑ l ∈ B, sg (w l) : ℤ) : ℝ) ^ 2 := by
            refine sum_le_sum (fun w hw => ?_)
            simp only [bad, mem_filter, mem_univ, true_and] at hw
            have : (rad n : ℝ) ≤ |((∑ l ∈ B, sg (w l) : ℤ) : ℝ)| := by exact_mod_cast hw
            calc (rad n : ℝ) ^ 2 ≤ |((∑ l ∈ B, sg (w l) : ℤ) : ℝ)| ^ 2 :=
                  pow_le_pow_left₀ hrpos.le this 2
              _ = _ := sq_abs _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
    have h2 : ∑ w : Oc → Bool, ((∑ l ∈ B, sg (w l) : ℤ) : ℝ) ^ 2 = B.card * D := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hsq
      push_cast at this; simpa [D] using this
    rw [h2] at h1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: no coordinates, every sum is `0 < rad`
      have : bad = ∅ := by
        rw [filter_eq_empty_iff]
        intro w _ hw
        have hB0 : B = ∅ := by
          rw [eq_empty_iff_forall_notMem]; intro l; have := l.1.isLt; omega
        rw [hB0, sum_empty, abs_zero] at hw
        have : (0 : ℤ) < rad n := by unfold rad; positivity
        omega
      rw [this]; simp; positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have : (bad.card : ℝ) * (4 * n) ≤ n * D := by nlinarith
      nlinarith
  -- good weights give two thresholds each
  have hgood : ∀ w : Oc → Bool, w ∉ bad →
      (2 : ℝ) ≤ ((univ.filter (fun t : Tset n =>
        0 ≤ (t : ℤ) - ∑ l ∈ B, sg (w l) ∧ (t : ℤ) - ∑ l ∈ B, sg (w l) ≤ 1)).card : ℝ) := by
    intro w hw
    simp only [bad, mem_filter, mem_univ, true_and, not_le] at hw
    exact_mod_cast card_t_ge (∑ l ∈ B, sg (w l)) hw
  have hcard : (Fintype.card (Oc → Bool) : ℝ) = D := by
    rw [Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
  calc (3 / 2 : ℝ) * D ≤ 2 * (D - bad.card) := by linarith
    _ = ∑ w ∈ univ \ bad, (2 : ℝ) := by
        rw [sum_const, card_sdiff, card_univ, inter_univ, nsmul_eq_mul,
          Nat.cast_sub (card_le_univ _), hcard]; ring
    _ ≤ ∑ w ∈ univ \ bad, ((univ.filter (fun t : Tset n =>
          0 ≤ (t : ℤ) - ∑ l ∈ B, sg (w l) ∧ (t : ℤ) - ∑ l ∈ B, sg (w l) ≤ 1)).card : ℝ) :=
        sum_le_sum (fun w hw => hgood w (by simpa using hw))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)

/-- The difference of two block sums is a signed sum over `A i ∪ A i'`. -/
lemma diff_eq (hA : ∀ i, A i ⊆ I) (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i'))
    {i i' : Fin M} (hii' : i ≠ i') (w : Oc → Bool) :
    ∑ l ∈ univ.filter (fun l : Oc => bpt x₀ A i l = true), sg (w l)
      - ∑ l ∈ univ.filter (fun l : Oc => bpt x₀ A i' l = true), sg (w l)
      = ∑ l ∈ (A i ∪ A i').subtype (fun l => l ∉ rows I x₀),
          (if (if (l : Fin n) ∈ A i then !x₀ l else x₀ l) then sg (w l) else - sg (w l)) := by
  classical
  rw [sum_filter, sum_filter, ← sum_sub_distrib]
  rw [← sum_subset (subset_univ ((A i ∪ A i').subtype (fun l => l ∉ rows I x₀)))
    (fun l _ hl => ?_)]
  · refine sum_congr rfl (fun l hl => ?_)
    simp only [mem_subtype, mem_union] at hl
    rcases hl with hl | hl
    · have hl' : (l : Fin n) ∉ A i' := Finset.disjoint_left.mp (hdisj i i' hii') hl
      cases hx : x₀ l <;> simp [bpt, hl, hl', hx, sg]
    · have hl' : (l : Fin n) ∉ A i := Finset.disjoint_right.mp (hdisj i i' hii') hl
      cases hx : x₀ l <;> simp [bpt, hl, hl', hx, sg]
  · simp only [mem_subtype, mem_union, not_or] at hl
    simp [bpt, hl.1, hl.2]

lemma card_D (hA : ∀ i, A i ⊆ I) (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i'))
    {s : ℕ} (hcard : ∀ i, (A i).card = s) {i i' : Fin M} (hii' : i ≠ i') :
    ((A i ∪ A i').subtype (fun l => l ∉ rows I x₀)).card = 2 * s := by
  classical
  rw [card_subtype]
  have : (A i ∪ A i').filter (fun l => l ∉ rows I x₀) = A i ∪ A i' := by
    apply filter_true_of_mem
    intro l hl
    simp only [rows, mem_filter, mem_univ, true_and, not_and, not_not]
    intro hlI
    rcases mem_union.mp hl with h | h
    · exact absurd (hA i h) hlI
    · exact absurd (hA i' h) hlI
  rw [this, card_union_of_disjoint (hdisj i i' hii'), hcard, hcard]; ring

/-- **Two blocks.** `Pr[sens_i ∧ sens_{i'}] ≤ 6·C(2s,s)/4^s / (2·rad+1)`, written as a count. -/
theorem card_pair_le (hA : ∀ i, A i ⊆ I) (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i'))
    {s : ℕ} (hcard : ∀ i, (A i).card = s) {i i' : Fin M} (hii' : i ≠ i') :
    ((univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')).card : ℝ)
      ≤ 6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s := by
  classical
  set Bi := univ.filter (fun l : Oc => bpt x₀ A i l = true)
  set Bi' := univ.filter (fun l : Oc => bpt x₀ A i' l = true)
  set D := (A i ∪ A i').subtype (fun l => l ∉ rows I x₀)
  set ε : Oc → Bool := fun l => if (l : Fin n) ∈ A i then !x₀ l else x₀ l
  have hD : D.card = 2 * s := card_D hA hdisj hcard hii'
  have heq : univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')
      = univ.filter (fun r : Rest (rows I x₀) =>
          (0 ≤ (r.2 : ℤ) - ∑ l ∈ Bi, sg (r.1 l) ∧ (r.2 : ℤ) - ∑ l ∈ Bi, sg (r.1 l) ≤ 1) ∧
          (0 ≤ (r.2 : ℤ) - ∑ l ∈ Bi', sg (r.1 l) ∧ (r.2 : ℤ) - ∑ l ∈ Bi', sg (r.1 l) ≤ 1)) := by
    ext r; simp only [mem_filter, mem_univ, true_and]; unfold sensR; rw [linR_eq, linR_eq]
  rw [heq, card_rest_split (I := I) (x₀ := x₀) (fun w t =>
    (0 ≤ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ≤ 1) ∧
    (0 ≤ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ≤ 1))]
  -- per weight: at most 2 thresholds, and none unless the two sums are within 1
  set close := univ.filter (fun w : Oc → Bool =>
    |∑ l ∈ Bi, sg (w l) - ∑ l ∈ Bi', sg (w l)| ≤ 1)
  have hper : ∀ w : Oc → Bool,
      ((univ.filter (fun t : Tset n =>
        (0 ≤ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ≤ 1) ∧
        (0 ≤ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ≤ 1))).card : ℝ)
        ≤ if w ∈ close then 2 else 0 := by
    intro w
    split_ifs with hw
    · have := card_t_le (n := n) (∑ l ∈ Bi, sg (w l))
      have h2 : (univ.filter (fun t : Tset n =>
          (0 ≤ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ≤ 1) ∧
          (0 ≤ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ≤ 1))).card ≤ 2 :=
        le_trans (card_le_card (by intro t ht; simp only [mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩))
          this
      exact_mod_cast h2
    · simp only [close, mem_filter, mem_univ, true_and, not_le] at hw
      norm_cast
      rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
      intro t _ ht
      have : |∑ l ∈ Bi, sg (w l) - ∑ l ∈ Bi', sg (w l)| ≤ 1 := by
        rw [abs_le]; constructor <;> omega
      exact absurd this (not_le.mpr hw)
  have hclose : (close.card : ℝ) ≤ 3 * ((2 * s).choose s : ℝ) * 2 ^ (Fintype.card Oc - 2 * s) := by
    have hsub : close ⊆ ({-1, 0, 1} : Finset ℤ).biUnion (fun v => univ.filter
        (fun w : Oc → Bool => ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)) = v)) := by
      intro w hw
      simp only [close, mem_filter, mem_univ, true_and] at hw
      rw [diff_eq hA hdisj hii' w] at hw
      have hw' : |∑ l ∈ D, (if ε l then sg (w l) else - sg (w l))| ≤ 1 := hw
      rw [mem_biUnion]
      refine ⟨∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)), ?_, by simp⟩
      simp only [mem_insert, mem_singleton]
      rw [abs_le] at hw'; omega
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := ({-1, 0, 1} : Finset ℤ)) (t := fun v => univ.filter
        (fun w : Oc → Bool => ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)) = v))
    have h3 : ∀ v ∈ ({-1, 0, 1} : Finset ℤ), (univ.filter
        (fun w : Oc → Bool => ∑ l ∈ D, (if ε l then sg (w l) else - sg (w l)) = v)).card
          ≤ (2 * s).choose s * 2 ^ (Fintype.card Oc - 2 * s) := by
      intro v _
      have := card_signsum_le (α := Oc) D ε v
      rwa [hD, show 2 * s / 2 = s by omega] at this
    have h4 := sum_le_sum h3
    rw [sum_const, show ({-1, 0, 1} : Finset ℤ).card = 3 by rfl, smul_eq_mul] at h4
    have : close.card ≤ 3 * ((2 * s).choose s * 2 ^ (Fintype.card Oc - 2 * s)) :=
      h1.trans (h2.trans h4)
    have : (close.card : ℝ) ≤ 3 * (((2 * s).choose s : ℝ) * 2 ^ (Fintype.card Oc - 2 * s)) := by
      exact_mod_cast this
    linarith
  have hDle : 2 * s ≤ Fintype.card Oc := by rw [← hD]; exact card_le_univ D
  have hpow : (2 : ℝ) ^ (Fintype.card Oc - 2 * s) = (2 : ℝ) ^ Fintype.card Oc / 4 ^ s := by
    rw [eq_div_iff (by positivity), show (4 : ℝ) ^ s = 2 ^ (2 * s) by
      rw [pow_mul]; norm_num, ← pow_add, Nat.sub_add_cancel hDle]
  calc ∑ w : Oc → Bool, ((univ.filter (fun t : Tset n =>
          (0 ≤ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi, sg (w l) ≤ 1) ∧
          (0 ≤ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ∧ (t : ℤ) - ∑ l ∈ Bi', sg (w l) ≤ 1))).card : ℝ)
      ≤ ∑ w : Oc → Bool, (if w ∈ close then (2 : ℝ) else 0) := sum_le_sum (fun w _ => hper w)
    _ = 2 * close.card := by rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * (3 * ((2 * s).choose s : ℝ) * 2 ^ (Fintype.card Oc - 2 * s)) := by linarith
    _ = 6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s := by rw [hpow]; ring

/-- **Bonferroni.** Private-gate density of block `i`. -/
theorem card_priv_ge (hA : ∀ i, A i ⊆ I) (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i'))
    {s : ℕ} (hcard : ∀ i, (A i).card = s) (i : Fin M) :
    (3 / 2 - 6 * ((M : ℝ) - 1) * ((2 * s).choose s : ℝ) / 4 ^ s) * 2 ^ Fintype.card Oc
      ≤ ((univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i)).card : ℝ) := by
  classical
  have hsub : univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i)
      ⊆ univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i)
        ∪ (univ.erase i).biUnion (fun i' => univ.filter
            (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    by_cases hp : privR (x₀ := x₀) (A := A) r i
    · exact mem_union_left _ (by simpa using hp)
    · apply mem_union_right
      unfold privR at hp
      push Not at hp
      obtain ⟨i', hi', hs'⟩ := hp hr
      exact mem_biUnion.mpr ⟨i', mem_erase.mpr ⟨hi', mem_univ _⟩, by simp [hr, hs']⟩
  have h1 := card_le_card hsub
  have h2 := card_union_le (univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i))
    ((univ.erase i).biUnion (fun i' => univ.filter
      (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')))
  have h3 := card_biUnion_le (s := univ.erase i) (t := fun i' => univ.filter
      (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i'))
  have h4 : ∑ i' ∈ univ.erase i, ((univ.filter
      (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')).card : ℝ)
        ≤ ∑ _i' ∈ univ.erase i, 6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s :=
    sum_le_sum (fun i' hi' => card_pair_le hA hdisj hcard (Ne.symm (ne_of_mem_erase hi')))
  rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
  have hsens := card_sens_ge (I := I) (x₀ := x₀) (A := A) i
  have hM : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) - 1 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exact absurd i.2 (by omega)
    · rw [Nat.cast_sub h]; simp
  have hall : ((univ.filter (fun r : Rest (rows I x₀) => sensR x₀ A r i)).card : ℝ)
      ≤ ((univ.filter (fun r : Rest (rows I x₀) => privR (x₀ := x₀) (A := A) r i)).card : ℝ)
        + ∑ i' ∈ univ.erase i, ((univ.filter
            (fun r : Rest (rows I x₀) => sensR x₀ A r i ∧ sensR x₀ A r i')).card : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_left h3 _))
  have hnn : 0 ≤ 6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s := by positivity
  have : ((M - 1 : ℕ) : ℝ) * (6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s)
      ≤ ((M : ℝ) - 1) * (6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s) :=
    mul_le_mul_of_nonneg_right hM hnn
  have e : (3 / 2 - 6 * ((M : ℝ) - 1) * ((2 * s).choose s : ℝ) / 4 ^ s) * 2 ^ Fintype.card Oc
      = 3 / 2 * 2 ^ Fintype.card Oc
        - ((M : ℝ) - 1) * (6 * ((2 * s).choose s : ℝ) * (2 : ℝ) ^ Fintype.card Oc / 4 ^ s) := by
    ring
  rw [e]; linarith

/-- With `16 M² ≤ s`, the Bonferroni loss is at most `0.9`. -/
lemma bonf_small {M s : ℕ} (hMs : 16 * M ^ 2 ≤ s) :
    6 * ((M : ℝ) - 1) * ((2 * s).choose s : ℝ) / 4 ^ s ≤ 9 / 10 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have h0 : (0 : ℝ) ≤ ((2 * s).choose s : ℝ) / 4 ^ s := by positivity
    have : 6 * (((0 : ℕ) : ℝ) - 1) * ((2 * s).choose s : ℝ) / 4 ^ s
        = -6 * (((2 * s).choose s : ℝ) / 4 ^ s) := by push_cast; ring
    rw [this]; nlinarith
  have hcb := centralBinom_sq_mul_le s
  rw [Nat.centralBinom_eq_two_mul_choose] at hcb
  have hcb' : ((2 * s).choose s : ℝ) ^ 2 * (3 * s + 1) ≤ (16 : ℝ) ^ s := by exact_mod_cast hcb
  set c : ℝ := ((2 * s).choose s : ℝ)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hs : (16 : ℝ) * M ^ 2 ≤ s := by exact_mod_cast hMs
  have h4 : (0 : ℝ) < 4 ^ s := by positivity
  have h16 : (16 : ℝ) ^ s = (4 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_le_iff₀ h4]
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- (6 (M-1) c)^2 ≤ 36 M^2 c^2 ≤ 36 M^2 16^s / (48 M^2 + 1) < (0.9 · 4^s)^2
  have key : (6 * ((M : ℝ) - 1) * c) ^ 2 ≤ (9 / 10 * 4 ^ s) ^ 2 := by
    have hc2 : c ^ 2 * (48 * (M : ℝ) ^ 2 + 1) ≤ (16 : ℝ) ^ s := by
      calc c ^ 2 * (48 * (M : ℝ) ^ 2 + 1) ≤ c ^ 2 * (3 * s + 1) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg c); linarith
        _ ≤ _ := hcb'
    rw [h16] at hc2
    have hMM : ((M : ℝ) - 1) ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg c, sq_nonneg ((4 : ℝ) ^ s), mul_le_mul_of_nonneg_left hMM (sq_nonneg c)]
  have hlhs : 0 ≤ 6 * ((M : ℝ) - 1) * c := by
    have : (0 : ℝ) ≤ (M : ℝ) - 1 := by linarith
    positivity
  have := (pow_le_pow_iff_left₀ hlhs (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp key
  linarith

end Density

end NLU

end

end ProblemQ
