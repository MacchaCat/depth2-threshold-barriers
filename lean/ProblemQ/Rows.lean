import ProblemQ.Smolensky

/-!
# Building blocks for Theorems NL / NL-U

* `card_many_le`: over independent coordinates `x : Fin R → Γ`, if each event `E r ⊆ Γ` has
  density `≤ p`, then at most `C(R,q) · p^q` of all `x` hit at least `q` of the events. This is
  used twice in Theorem NL-U: for the `M` points of a row, and for the `R` rows of a frame.
* `centralBinom_sq_mul_le`: `C(2h,h)² (3h+1) ≤ 16^h`, hence `C(F,⌊F/2⌋)² F ≤ 4^F`.
* `two_mul_card_low_le`: `2 · #{M : |M| ≤ ⌊F/2⌋ + d} ≤ 2^F + (2d+1) C(F,⌊F/2⌋)`.
* `smolensky_prob`: a degree-`d` function agrees with the median threshold on at most a
  `½ + (d+1)/√F` fraction of the cube.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

section Rows

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Points of `Fin R → Γ` hitting every event indexed by `T`. -/
lemma card_hit_all (R : ℕ) (E : Fin R → Finset Γ) (T : Finset (Fin R)) :
    ((univ.filter (fun x : Fin R → Γ => ∀ r ∈ T, x r ∈ E r)).card : ℝ)
      = ∏ r, (if r ∈ T then ((E r).card : ℝ) else (Fintype.card Γ : ℝ)) := by
  classical
  have hP := Fintype.prod_sum (fun (r : Fin R) (γ : Γ) =>
    if r ∈ T then (if γ ∈ E r then (1 : ℝ) else 0) else 1)
  have hl : ∀ x : Fin R → Γ, ∏ r, (if r ∈ T then (if x r ∈ E r then (1 : ℝ) else 0) else 1)
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

/-- **Many independent events.** If each event has density `≤ p`, at most `C(R,q) p^q |Γ|^R`
points hit at least `q` of them. -/
theorem card_many_le (R q : ℕ) (E : Fin R → Finset Γ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ r, ((E r).card : ℝ) ≤ p * Fintype.card Γ) :
    ((univ.filter (fun x : Fin R → Γ =>
        q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card : ℝ)
      ≤ (R.choose q : ℝ) * p ^ q * (Fintype.card Γ : ℝ) ^ R := by
  classical
  set C : ℝ := (Fintype.card Γ : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  -- every such point hits all events of some `q`-subset
  have hsub : univ.filter (fun x : Fin R → Γ => q ≤ (univ.filter (fun r => x r ∈ E r)).card)
      ⊆ (univ.powersetCard q).biUnion
          (fun T => univ.filter (fun x : Fin R → Γ => ∀ r ∈ T, x r ∈ E r)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hx
    rw [mem_biUnion]
    refine ⟨T, mem_powersetCard.mpr ⟨subset_univ _, hTc⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro r hr
    have := hT hr
    simpa using this
  have hone : ∀ T ∈ (univ : Finset (Fin R)).powersetCard q,
      ((univ.filter (fun x : Fin R → Γ => ∀ r ∈ T, x r ∈ E r)).card : ℝ) ≤ p ^ q * C ^ R := by
    intro T hT
    have hTc : T.card = q := (mem_powersetCard.mp hT).2
    rw [card_hit_all]
    calc ∏ r, (if r ∈ T then ((E r).card : ℝ) else C)
        ≤ ∏ r, (if r ∈ T then p * C else C) := by
          apply prod_le_prod₀
          · intro r _; split_ifs <;> positivity
          · intro r _; split_ifs
            · exact hp r
            · exact le_refl _
      _ = p ^ q * C ^ R := by
          rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, hTc,
            mul_pow]
          have h1 : (univ.filter (fun r : Fin R => r ∉ T)).card = R - q := by
            have := card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
              (fun r => r ∈ T)
            rw [filter_mem_eq_inter, univ_inter, hTc, card_univ, Fintype.card_fin] at this
            omega
          rw [h1]
          have hqR : q ≤ R := by
            have := card_le_univ T; rw [Fintype.card_fin] at this; omega
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hqR]
  calc ((univ.filter (fun x : Fin R → Γ =>
          q ≤ (univ.filter (fun r => x r ∈ E r)).card)).card : ℝ)
      ≤ (((univ.powersetCard q).biUnion
          (fun T => univ.filter (fun x : Fin R → Γ => ∀ r ∈ T, x r ∈ E r))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ T ∈ (univ : Finset (Fin R)).powersetCard q,
          ((univ.filter (fun x : Fin R → Γ => ∀ r ∈ T, x r ∈ E r)).card : ℝ) := by
        rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
    _ ≤ ∑ _T ∈ (univ : Finset (Fin R)).powersetCard q, p ^ q * C ^ R := sum_le_sum hone
    _ = (R.choose q : ℝ) * p ^ q * C ^ R := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Rows

section Binomial

/-- `C(2h,h)² (3h+1) ≤ 16^h`. -/
lemma centralBinom_sq_mul_le (h : ℕ) : Nat.centralBinom h ^ 2 * (3 * h + 1) ≤ 16 ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hrec := Nat.succ_mul_centralBinom_succ h
    -- (h+1)² (3h+1) · [cb(h+1)² (3h+4)] = 4(2h+1)²(3h+4) · [cb h² (3h+1)]
    have key : ((h + 1) ^ 2 * (3 * h + 1)) * (Nat.centralBinom (h + 1) ^ 2 * (3 * (h + 1) + 1))
        ≤ ((h + 1) ^ 2 * (3 * h + 1)) * 16 ^ (h + 1) := by
      have e : ((h + 1) ^ 2 * (3 * h + 1)) * (Nat.centralBinom (h + 1) ^ 2 * (3 * (h + 1) + 1))
          = (4 * (2 * h + 1) ^ 2 * (3 * h + 4)) * (Nat.centralBinom h ^ 2 * (3 * h + 1)) := by
        have : ((h + 1) * Nat.centralBinom (h + 1)) ^ 2
            = (2 * (2 * h + 1) * Nat.centralBinom h) ^ 2 := by rw [hrec]
        nlinarith [this]
      rw [e]
      calc (4 * (2 * h + 1) ^ 2 * (3 * h + 4)) * (Nat.centralBinom h ^ 2 * (3 * h + 1))
          ≤ (4 * (2 * h + 1) ^ 2 * (3 * h + 4)) * 16 ^ h := Nat.mul_le_mul_left _ ih
        _ ≤ ((h + 1) ^ 2 * (3 * h + 1)) * 16 ^ (h + 1) := by
            rw [pow_succ]
            have : 4 * (2 * h + 1) ^ 2 * (3 * h + 4) ≤ (h + 1) ^ 2 * (3 * h + 1) * 16 := by
              ring_nf; omega
            calc (4 * (2 * h + 1) ^ 2 * (3 * h + 4)) * 16 ^ h
                ≤ ((h + 1) ^ 2 * (3 * h + 1) * 16) * 16 ^ h := Nat.mul_le_mul_right _ this
              _ = ((h + 1) ^ 2 * (3 * h + 1)) * (16 ^ h * 16) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- `C(F,⌊F/2⌋)² · F ≤ 4^F`. -/
lemma choose_half_sq_mul_le (F : ℕ) : (F.choose (F / 2)) ^ 2 * F ≤ 4 ^ F := by
  rcases Nat.even_or_odd F with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · have hh : (h + h) / 2 = h := by omega
    rw [hh, show h + h = 2 * h by ring, ← Nat.centralBinom_eq_two_mul_choose]
    have := centralBinom_sq_mul_le h
    calc Nat.centralBinom h ^ 2 * (2 * h) ≤ Nat.centralBinom h ^ 2 * (3 * h + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ h := this
      _ = 4 ^ (2 * h) := by rw [pow_mul]; norm_num
  · have hh : (2 * h + 1) / 2 = h := by omega
    rw [hh]
    -- C(2h+1, h) * 2 = C(2h+2, h+1)
    have hc : (2 * h + 1).choose h * 2 = Nat.centralBinom (h + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (h + 1) = (2 * h + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have := centralBinom_sq_mul_le (h + 1)
    have h2 : ((2 * h + 1).choose h) ^ 2 * 4 * (3 * (h + 1) + 1) ≤ 16 ^ (h + 1) := by
      calc ((2 * h + 1).choose h) ^ 2 * 4 * (3 * (h + 1) + 1)
          = ((2 * h + 1).choose h * 2) ^ 2 * (3 * (h + 1) + 1) := by ring
        _ ≤ 16 ^ (h + 1) := by rw [hc]; exact this
    have h3 : ((2 * h + 1).choose h) ^ 2 * (2 * h + 1) * 4 * 4
        ≤ ((2 * h + 1).choose h) ^ 2 * 4 * (3 * (h + 1) + 1) * 4 := by
      have : (2 * h + 1) * 4 ≤ 3 * (h + 1) + 1 + 3 * (h + 1) + 1 + 3 * (h + 1) + 1 + 3 * h + 1 := by
        omega
      nlinarith [Nat.zero_le (((2 * h + 1).choose h) ^ 2)]
    have h4 : 4 ^ (2 * h + 1) * 4 = 16 ^ (h + 1) := by
      rw [show 16 = 4 ^ 2 by norm_num, ← pow_mul, ← pow_succ]; ring_nf
    nlinarith [h2, h3, h4]

end Binomial

namespace Smolensky

variable {F : ℕ}

/-- Number of subsets of size exactly `i`. -/
lemma card_layer (i : ℕ) :
    (univ.filter (fun M : Finset (Fin F) => M.card = i)).card = F.choose i := by
  rw [show univ.filter (fun M : Finset (Fin F) => M.card = i) = univ.powersetCard i by
    ext M; simp [mem_powersetCard]]
  rw [card_powersetCard, card_univ, Fintype.card_fin]

/-- `2 · #{M : |M| ≤ ⌊F/2⌋} ≤ 2^F + C(F,⌊F/2⌋)`. -/
lemma two_mul_card_half_le :
    2 * (univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2)).card
      ≤ 2 ^ F + F.choose (F / 2) := by
  classical
  set A := univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2)
  set B := univ.filter (fun M : Finset (Fin F) => F - F / 2 ≤ M.card)
  have hAB : A.card = B.card := by
    refine card_bij (fun M _ => Mᶜ) ?_ ?_ ?_
    · intro M hM
      simp only [A, B, mem_filter, mem_univ, true_and] at hM ⊢
      rw [card_compl, Fintype.card_fin]; omega
    · intro M _ N _ h; exact compl_injective h
    · intro N hN
      refine ⟨Nᶜ, ?_, compl_compl N⟩
      simp only [A, B, mem_filter, mem_univ, true_and] at hN ⊢
      rw [card_compl, Fintype.card_fin]; omega
  have hunion : A ∪ B = univ := by
    ext M; simp only [A, B, mem_union, mem_filter, mem_univ, true_and, iff_true]; omega
  have hinter : (A ∩ B).card ≤ F.choose (F / 2) := by
    rw [← card_layer (F := F) (F / 2)]
    apply card_le_card
    intro M hM
    simp only [A, B, mem_inter, mem_filter, mem_univ, true_and] at hM ⊢
    omega
  have := card_union_add_card_inter A B
  rw [hunion, card_univ, Fintype.card_finset, Fintype.card_fin] at this
  omega

/-- `2 · #{M : |M| ≤ ⌊F/2⌋ + d} ≤ 2^F + (2d+1) C(F,⌊F/2⌋)`. -/
lemma two_mul_card_low_le (d : ℕ) :
    2 * (univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2 + d)).card
      ≤ 2 ^ F + (2 * d + 1) * F.choose (F / 2) := by
  classical
  induction d with
  | zero => simpa using two_mul_card_half_le (F := F)
  | succ d ih =>
    have hsplit : univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2 + (d + 1))
        ⊆ univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2 + d)
          ∪ univ.filter (fun M : Finset (Fin F) => M.card = F / 2 + (d + 1)) := by
      intro M hM; simp only [mem_filter, mem_univ, true_and, mem_union] at hM ⊢; omega
    have h1 := card_le_card hsplit
    have h2 := card_union_le (univ.filter (fun M : Finset (Fin F) => M.card ≤ F / 2 + d))
      (univ.filter (fun M : Finset (Fin F) => M.card = F / 2 + (d + 1)))
    rw [card_layer] at h2
    have h3 : F.choose (F / 2 + (d + 1)) ≤ F.choose (F / 2) := Nat.choose_le_middle _ _
    nlinarith

/-- **Smolensky, probability form.** A degree-`d` function agrees with the median threshold on
at most a `½ + (d+1)/√F` fraction of `{0,1}^F` (`F ≥ 1`). -/
theorem smolensky_prob (hF : 1 ≤ F) {d : ℕ} {Q : (Fin F → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    ((univ.filter (fun β : Fin F → Bool => Q β = TH β)).card : ℝ) / 2 ^ F
      ≤ 1 / 2 + (d + 1) / Real.sqrt F := by
  classical
  have h1 := smolensky hQ
  have h2 := two_mul_card_low_le (F := F) d
  have h3 := choose_half_sq_mul_le F
  have h3' : ((F.choose (F / 2) : ℕ) : ℝ) ^ 2 * (F : ℝ) ≤ (4 : ℝ) ^ F := by exact_mod_cast h3
  have hA0 : (((univ.filter (fun β : Fin F → Bool => Q β = TH β)).card * 2 : ℕ) : ℝ)
      ≤ ((2 ^ F + (2 * d + 1) * F.choose (F / 2) : ℕ) : ℝ) := by
    have : (univ.filter (fun β : Fin F → Bool => Q β = TH β)).card * 2
        ≤ 2 ^ F + (2 * d + 1) * F.choose (F / 2) := by omega
    exact_mod_cast this
  push_cast at hA0
  set c : ℝ := (F.choose (F / 2) : ℝ)
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hsq : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF'
  have h2F : (0 : ℝ) < 2 ^ F := by positivity
  -- c ≤ 2^F / √F
  have hc : c * Real.sqrt F ≤ 2 ^ F := by
    have : c ^ 2 * F ≤ ((2 : ℝ) ^ F) ^ 2 := by
      have e : ((2 : ℝ) ^ F) ^ 2 = (4 : ℝ) ^ F := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [e]; exact h3'
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    have : (c * Real.sqrt F) ^ 2 ≤ ((2 : ℝ) ^ F) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hF'.le]; exact this
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  have hA : ((univ.filter (fun β : Fin F → Bool => Q β = TH β)).card : ℝ) * 2
      ≤ 2 ^ F + (2 * d + 1) * c := hA0
  rw [div_le_iff₀ h2F]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have key : (2 * (d : ℝ) + 1) * c ≤ 2 * ((d + 1) / Real.sqrt F) * 2 ^ F := by
    rw [show 2 * ((d + 1) / Real.sqrt F) * 2 ^ F = 2 * (d + 1) * (2 ^ F / Real.sqrt F) by ring]
    have hc' : c ≤ 2 ^ F / Real.sqrt F := by rw [le_div_iff₀ hsq]; exact hc
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    calc (2 * (d : ℝ) + 1) * c ≤ 2 * (d + 1) * c := by nlinarith
      _ ≤ 2 * (d + 1) * (2 ^ F / Real.sqrt F) := by gcongr
  nlinarith

end Smolensky

end

end ProblemQ
