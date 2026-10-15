import ProblemQ.Atom

/-!
# Theorem 3′ (oblivious window barrier), fully instantiated

For `k = 2h + 3`, if `m ≥ 5800 (4⌊√n⌋ + 5) n²`, `8 C(k,3)² ≤ n²`, `8 (2n)^k ≤ e^{C(k,3)}`,
`L ≤ 2^k`, every list entry has `|supp α| ≥ m/2`, the window is `W ≤ n` and the allowed bad
fraction satisfies `4 δ m² ≤ n²`, then at least half of all random circuits defeat the list:
no live set of size `k` has half of its columns certified.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

lemma exp_three_le : Real.exp 3 ≤ 20.1 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
    _ ≤ 20.1 := by norm_num

/-- The per-column bound collapses to `2 e^{-N}`. -/
lemma rhs_le {N b a : ℝ} (hN : 0 < N) (hb : 4 * N ≤ b) (hab : Real.exp 3 * b ≤ a) :
    Real.exp (N / 2) * ((b / (b + a)) ^ (N / 2)
      + 2 ^ (N / 2) * Real.exp (-b / (2 * 1 ^ 2))) ≤ 2 * Real.exp (-N) := by
  have hbpos : 0 < b := by linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hab
  have h1 : b / (b + a) ≤ Real.exp (-3) := by
    rw [div_le_iff₀ (by positivity), Real.exp_neg]
    have : b ≤ (Real.exp 3)⁻¹ * (b + a) := by
      rw [inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 3)]
      nlinarith [Real.exp_pos 3]
    linarith
  have t1 : (b / (b + a)) ^ (N / 2) ≤ Real.exp (-(3 * N / 2)) := by
    calc (b / (b + a)) ^ (N / 2) ≤ Real.exp (-3) ^ (N / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = Real.exp (-(3 * N / 2)) := by rw [← Real.exp_mul]; ring_nf
  have t2 : (2 : ℝ) ^ (N / 2) ≤ Real.exp (N / 2) := by
    calc (2 : ℝ) ^ (N / 2) ≤ Real.exp 1 ^ (N / 2) :=
          Real.rpow_le_rpow (by norm_num)
            (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by positivity)
      _ = Real.exp (N / 2) := by rw [← Real.exp_mul, one_mul]
  have t3 : Real.exp (-b / (2 * 1 ^ 2)) ≤ Real.exp (-(2 * N)) :=
    Real.exp_le_exp.mpr (by norm_num; linarith)
  calc Real.exp (N / 2) * ((b / (b + a)) ^ (N / 2) + 2 ^ (N / 2) * Real.exp (-b / (2 * 1 ^ 2)))
      ≤ Real.exp (N / 2) * (Real.exp (-(3 * N / 2)) + Real.exp (N / 2) * Real.exp (-(2 * N))) := by
        gcongr
    _ = 2 * Real.exp (-N) := by
        rw [mul_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf

/-- Monotonicity of certification in the window. -/
lemma certified_mono {n m : ℕ} {T : Finset ℤ} {ω : Fin m → Gate n T} {α : Fin m → ℝ}
    {I : Finset (Fin n)} {z : Fin n → Bool} {c : (I → Bool) → ℝ} {W W' δ : ℝ} (hW : W ≤ W')
    (h : certified T ω α I z c W δ) : certified T ω α I z c W' δ := by
  unfold certified at *
  refine le_trans ?_ h
  exact_mod_cast card_le_card (fun y hy => by
    simp only [mem_filter, mem_univ, true_and] at hy ⊢; linarith)

lemma succeeds_mono {n m L k : ℕ} {T : Finset ℤ} {ω : Fin m → Gate n T}
    {α : Fin L → Fin m → ℝ} {c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ}
    {W W' δ : ℝ} (hW : W ≤ W') (h : succeeds T k ω α c W δ) : succeeds T k ω α c W' δ := by
  obtain ⟨I, hI, hf⟩ := h
  refine ⟨I, hI, le_trans hf ?_⟩
  unfold certFrac
  gcongr
  apply certified_mono hW

/-- `f · C(2h+3, 3) ≥ 1/48` for `f = 1/(64 h (h+1)^2)`. -/
lemma f_mul_N (h : ℕ) (hh : 1 ≤ h) :
    1 / 48 ≤ 1 / (64 * (h : ℝ) * (h + 1) ^ 2) * ((2 * h + 3).choose 3 : ℝ) := by
  have hc : ((2 * h + 3).choose 3 : ℝ) * 6 = (2 * h + 3) * (2 * h + 2) * (2 * h + 1) := by
    have := Nat.descFactorial_eq_factorial_mul_choose (2 * h + 3) 3
    have hd : (2 * h + 3).descFactorial 3 = (2 * h + 3) * (2 * h + 2) * (2 * h + 1) := by
      simp [Nat.descFactorial]; ring
    rw [hd] at this
    have : ((2 * h + 3) * (2 * h + 2) * (2 * h + 1) : ℕ) = 6 * (2 * h + 3).choose 3 := by
      rw [this]; simp [Nat.factorial]
    have := congrArg (fun x : ℕ => (x : ℝ)) this
    push_cast at this; linarith
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [hc]

open Classical in
/-- **Theorem 3′, explicit form.** The list succeeds on at most a `4 (2n)^k e^{-C(k,3)}` fraction. -/
theorem barrier_bound (n h m L : ℕ) (hh : 1 ≤ h)
    (hN2 : 8 * (((2 * h + 3).choose 3 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2)
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    (hL : L ≤ 2 ^ (2 * h + 3))
    (α : Fin L → Fin m → ℝ) (hα : ∀ a i, α a i = 1 ∨ α a i = -1 ∨ α a i = 0)
    (hsupp : ∀ a, (m : ℝ) ≤ 2 * ((univ.filter (fun i => α a i ≠ 0)).card : ℝ))
    (c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) {W δ : ℝ} (hW0 : 0 < W)
    (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        succeeds (Tset n) (2 * h + 3) ω α c W δ)).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m
      ≤ 4 * (2 * (n : ℝ)) ^ (2 * h + 3) * Real.exp (-(((2 * h + 3).choose 3 : ℕ) : ℝ)) := by
  classical
  set k := 2 * h + 3 with hk
  set N : ℝ := ((k.choose 3 : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast Nat.choose_pos (by omega)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have hnpos : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hn2; simp at hn2
  set G : ℝ := (Fintype.card (Gate n (Tset n)) : ℝ) ^ m with hG
  have hGpos : 0 < G := by
    have : 0 < Fintype.card (Gate n (Tset n)) := Fintype.card_pos
    positivity
  -- reduce to window `n`
  have hsub : univ.filter (fun ω : Fin m → Gate n (Tset n) => succeeds (Tset n) k ω α c W δ)
      ⊆ univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          succeeds (Tset n) k ω α c (n : ℝ) δ) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact succeeds_mono hWn hω
  -- per-column bound
  have hB : ∀ I : Finset (Fin n), I.card = k → ∀ z a,
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        certified (Tset n) ω (α a) I z (c a I) (n : ℝ) δ)).card : ℝ)
        ≤ 2 * Real.exp (-N) * G := by
    intro I hI z a
    have hcol := column_bound (Tset n) I h hh hI z (α a) (hα a) (c a I) hnpos hδ0
    have hcardL : (Fintype.card (L3 I) : ℝ) = N := by
      rw [card_L3, hNdef]; simp [hI]
    rw [hcardL] at hcol
    rw [div_le_iff₀ hGpos] at hcol
    refine hcol.trans (mul_le_mul_of_nonneg_right ?_ hGpos.le)
    set R2 := Real.sqrt ((n : ℝ) ^ 2 + 4 * δ * (m : ℝ) ^ 2) ^ 2 with hR2
    have hR2eq : R2 = (n : ℝ) ^ 2 + 4 * δ * (m : ℝ) ^ 2 := by
      rw [hR2, Real.sq_sqrt (by positivity)]
    apply rhs_le hNpos
    · -- 4N ≤ R2 / (2N)
      rw [le_div_iff₀ (by positivity), hR2eq]
      nlinarith [mul_nonneg hδ0 (sq_nonneg (m : ℝ))]
    · -- e^3 b ≤ a
      have hp := pAtom_ge (n := n) I z
      have hf := f_mul_N h hh
      have hs := hsupp a
      have he := exp_three_le
      have hrad : (2 * (rad n : ℝ) + 1) = 4 * (Nat.sqrt n : ℝ) + 5 := by
        unfold rad; push_cast; ring
      rw [hrad] at hp
      set p := pAtom (Tset n) I z with hpdef
      set s := ((univ.filter (fun i => α a i ≠ 0)).card : ℝ) with hsdef
      set f : ℝ := 1 / (64 * (h : ℝ) * (h + 1) ^ 2) with hfdef
      set q : ℝ := 4 * (Nat.sqrt n : ℝ) + 5 with hqdef
      have hq : 0 < q := by positivity
      have hp0 : 0 ≤ p := le_trans (by positivity) hp
      have hpq : 3 / 4 ≤ p * q := by rwa [div_le_iff₀ hq] at hp
      have hs2 : 2900 * q * (n : ℝ) ^ 2 ≤ s := by linarith
      have hps : 2175 * (n : ℝ) ^ 2 ≤ p * s := by
        calc 2175 * (n : ℝ) ^ 2 = 2900 * (n : ℝ) ^ 2 * (3 / 4) := by ring
          _ ≤ 2900 * (n : ℝ) ^ 2 * (p * q) := by gcongr
          _ = p * (2900 * q * (n : ℝ) ^ 2) := by ring
          _ ≤ p * s := by gcongr
      have hfN : 1 / 48 ≤ f * N := by rw [hNdef, hk]; exact hf
      have hR2le : R2 ≤ 2 * (n : ℝ) ^ 2 := by rw [hR2eq]; linarith
      have hR20 : 0 ≤ R2 := by rw [hR2]; positivity
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      calc Real.exp 3 * R2 ≤ 20.1 * (2 * (n : ℝ) ^ 2) :=
            mul_le_mul he hR2le hR20 (by norm_num)
        _ ≤ 2 * (43 / 96) * (2175 * (n : ℝ) ^ 2) * (1 / 48) := by nlinarith
        _ ≤ 2 * (43 / 96) * (p * s) * (f * N) := by gcongr
        _ = 43 / 96 * (p * f) * s * (2 * N) := by ring
  -- union bound and arithmetic
  have hmain := succeeds_bound (Tset n) k α c (n : ℝ) δ (2 * Real.exp (-N)) hB
  have hcount := (Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)
  rw [div_le_iff₀ hGpos]
  refine hcount.trans (hmain.trans ?_)
  have hchoose : ((n.choose k : ℕ) : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hLk : (L : ℝ) ≤ 2 ^ k := by exact_mod_cast hL
  calc 2 * ((n.choose k : ℕ) : ℝ) * L * (2 * Real.exp (-N)) * G
      ≤ 2 * (n : ℝ) ^ k * 2 ^ k * (2 * Real.exp (-N)) * G := by gcongr
    _ = (4 * (2 * (n : ℝ)) ^ k * Real.exp (-N)) * G := by rw [mul_pow]; ring

open Classical in
/-- **Theorem 3′.** -/
theorem barrier (n h m L : ℕ) (hh : 1 ≤ h)
    (hN2 : 8 * (((2 * h + 3).choose 3 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2)
    (hexp : 8 * (2 * (n : ℝ)) ^ (2 * h + 3) ≤ Real.exp ((2 * h + 3).choose 3))
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    (hL : L ≤ 2 ^ (2 * h + 3))
    (α : Fin L → Fin m → ℝ) (hα : ∀ a i, α a i = 1 ∨ α a i = -1 ∨ α a i = 0)
    (hsupp : ∀ a, (m : ℝ) ≤ 2 * ((univ.filter (fun i => α a i ≠ 0)).card : ℝ))
    (c : Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) {W δ : ℝ} (hW0 : 0 < W)
    (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        succeeds (Tset n) (2 * h + 3) ω α c W δ)).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m ≤ 1 / 2 := by
  refine (barrier_bound n h m L hh hN2 hm hL α hα hsupp c hW0 hWn hδ0 hδ).trans ?_
  set N : ℝ := (((2 * h + 3).choose 3 : ℕ) : ℝ)
  have hexpN : 8 * (2 * (n : ℝ)) ^ (2 * h + 3) ≤ Real.exp N := by simpa using hexp
  have hE : Real.exp (-N) * Real.exp N = 1 := by rw [← Real.exp_add]; simp
  have := mul_le_mul_of_nonneg_right hexpN (Real.exp_pos (-N)).le
  nlinarith [Real.exp_pos (-N)]

open Classical in
/-- **Bounded-information adaptivity.** The list may be *selected after seeing the circuit*
from a family of `F` candidate lists fixed in advance. If `8 F (2n)^k ≤ e^{C(k,3)}`, then on at
least half of all circuits no list of the family succeeds. -/
theorem barrier_family (n h m L F : ℕ) (hh : 1 ≤ h)
    (hN2 : 8 * (((2 * h + 3).choose 3 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2)
    (hexp : 8 * (F : ℝ) * (2 * (n : ℝ)) ^ (2 * h + 3) ≤ Real.exp ((2 * h + 3).choose 3))
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    (hL : L ≤ 2 ^ (2 * h + 3))
    (α : Fin F → Fin L → Fin m → ℝ) (hα : ∀ f a i, α f a i = 1 ∨ α f a i = -1 ∨ α f a i = 0)
    (hsupp : ∀ f a, (m : ℝ) ≤ 2 * ((univ.filter (fun i => α f a i ≠ 0)).card : ℝ))
    (c : Fin F → Fin L → ∀ I : Finset (Fin n), (I → Bool) → ℝ) {W δ : ℝ} (hW0 : 0 < W)
    (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ f, succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ)).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m ≤ 1 / 2 := by
  set G : ℝ := (Fintype.card (Gate n (Tset n)) : ℝ) ^ m with hG
  have hGpos : 0 < G := by
    have : 0 < Fintype.card (Gate n (Tset n)) := Fintype.card_pos
    positivity
  set N : ℝ := (((2 * h + 3).choose 3 : ℕ) : ℝ)
  set Bd : ℝ := 4 * (2 * (n : ℝ)) ^ (2 * h + 3) * Real.exp (-N) with hBd
  have hone : ∀ f, ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
      succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ)).card : ℝ) ≤ Bd * G := by
    intro f
    have := barrier_bound n h m L hh hN2 hm hL (α f) (hα f) (hsupp f) (c f) hW0 hWn hδ0 hδ
    rwa [div_le_iff₀ hGpos] at this
  have hU : univ.filter (fun ω : Fin m → Gate n (Tset n) =>
      ∃ f, succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ)
      = univ.biUnion (fun f => univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ)) := by
    ext ω; simp
  rw [hU, div_le_iff₀ hGpos]
  calc ((univ.biUnion (fun f => univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ))).card : ℝ)
      ≤ ∑ f : Fin F, ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          succeeds (Tset n) (2 * h + 3) ω (α f) (c f) W δ)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _f : Fin F, Bd * G := sum_le_sum (fun f _ => hone f)
    _ = F * Bd * G := by simp; ring
    _ ≤ 1 / 2 * G := by
        apply mul_le_mul_of_nonneg_right _ hGpos.le
        have hexpN : 8 * (F : ℝ) * (2 * (n : ℝ)) ^ (2 * h + 3) ≤ Real.exp N := by simpa using hexp
        have hE : Real.exp (-N) * Real.exp N = 1 := by rw [← Real.exp_add]; simp
        have := mul_le_mul_of_nonneg_right hexpN (Real.exp_pos (-N)).le
        rw [hBd]
        nlinarith [Real.exp_pos (-N)]

end

end ProblemQ
