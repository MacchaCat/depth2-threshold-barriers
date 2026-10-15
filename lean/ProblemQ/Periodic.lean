import ProblemQ.Restrict
import ProblemQ.Uniform

/-!
# Lemma PS (periodic Smolensky), probability part

Target `bit(K + |β|) = ⌊(K + |β|)/h⌋ mod 2` (for `h = 2^t` this is `bit_t`). A polynomial of
`F₂`-degree `≤ d ≤ h/200 - 1` agrees with it on at most `93%` of `{0,1}^F` once `F ≥ 2600 h²`.

Proof (Lean form; no Fourier analysis):
* split `β = (β', β'')` with `|β'| = 2a`, `a = ⌊h²/13⌋`;
* for fixed `β''`, put `c = K + |β''|`. If the transition `θ ≡ -c (mod h)` closest to `a` is within
  `g = ⌊h/5⌋` of `a`, then on the window `|β'| ∈ [θ-h, θ+h)` the target is `TH_θ` or `1 + TH_θ`
  (`bitAt_window`). Outside the window lies a Chernoff tail (`card_high_le`, `card_low_le`).
  Inside, offset Smolensky (`smolensky_gen`, `smolensky_gen_compl`) applies (`slice_bound`,
  `slice_real`);
* average over `|β''| ~ Bin(N)`: `binom_avg` compares with the uniform residue up to
  `h · C(N, N/2) / 2`, using only unimodality of the binomial coefficients.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace Periodic

open Smolensky

/-- The periodic target: bit `⌊(K + c)/h⌋ mod 2`. -/
def bitAt (h K c : ℕ) : ZMod 2 := if (K + c) / h % 2 = 1 then 1 else 0

/-! ### One transition -/

/-- Inside the window `[θ-h, θ+h)` around a transition `θ` (`h ∣ c + θ`) the target is a single
threshold, possibly complemented. -/
lemma bitAt_window {h c θ x : ℕ} (hθ : h ≤ θ) (hdiv : (c + θ) % h = 0)
    (hlo : θ ≤ x + h) (hhi : x < θ + h) :
    bitAt h c x = (if (c + θ) / h % 2 = 1 then 0 else 1) + (if θ ≤ x then 1 else 0) := by
  set q := (c + θ) / h with hq
  have hcq : c + θ = q * h := by
    have := Nat.div_add_mod (c + θ) h
    rw [hdiv, add_zero] at this; rw [hq]; linarith
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, zero_mul] at hcq; omega
    · exact h0
  unfold bitAt
  by_cases hx : θ ≤ x
  · have hd : (c + x) / h = q := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    rw [hd, if_pos hx]
    rcases Nat.mod_two_eq_zero_or_one q with h2 | h2 <;> simp [h2] <;> decide
  · have hd : (c + x) / h = q - 1 := by
      apply Nat.div_eq_of_lt_le
      · have : (q - 1) * h + h = q * h := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq1]
        omega
      · have : (q - 1 + 1) * h = q * h := by rw [Nat.sub_add_cancel hq1]
        omega
    rw [hd, if_neg hx]
    have hpar : (q - 1) % 2 = 1 ↔ ¬ q % 2 = 1 := by omega
    by_cases h2 : q % 2 = 1
    · have : ¬ (q - 1) % 2 = 1 := fun h' => hpar.mp h' h2
      simp [this, h2]
    · have : (q - 1) % 2 = 1 := hpar.mpr h2
      simp [this, h2]

/-! ### Chernoff tails for `|β'|` -/

section Tails

variable {a : ℕ}

/-- `±1` sign of a coordinate. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sum_sgn (β : Fin (2 * a) → Bool) :
    ∑ i, sgn (β i) = 2 * ((ones β).card : ℝ) - 2 * a := by
  classical
  unfold sgn ones
  rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * a))))
    (fun i => β i = true)
  rw [card_univ, Fintype.card_fin] at h
  have h' : ((univ.filter (fun i => β i = true)).card : ℝ)
      + ((univ.filter (fun i => ¬ β i = true)).card : ℝ) = 2 * a := by exact_mod_cast h
  simp only [Bool.not_eq_true] at h' ⊢
  have e : (univ.filter (fun i => β i = true)) = univ.filter (fun i => β i = true) := rfl
  linarith

/-- Upper tail: `#{β' : |β'| ≥ a + D} ≤ 2^{2a} e^{-D²/(2a)}`. -/
lemma card_high_le (D : ℕ) (ha : 0 < a) (hD : D ≤ 2 * a) :
    ((univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)).card : ℝ)
      ≤ 2 ^ (2 * a) * Real.exp (-((D : ℝ) ^ 2 / (2 * a))) := by
  classical
  have hA : (0 : ℝ) < 2 * a := by positivity
  set lam : ℝ := D / (2 * a) with hlam
  have h0 : 0 ≤ lam := by positivity
  have h1 : lam ≤ 1 := by
    rw [div_le_one hA]; exact_mod_cast hD
  have hg : ∀ b, |sgn b| ≤ 1 := by intro b; cases b <;> simp [sgn]
  have hsum : ∑ b, sgn b ≤ (Fintype.card Bool : ℝ) * 0 := by simp [sgn]
  have hsq : ∑ b, sgn b ^ 2 ≤ (Fintype.card Bool : ℝ) * 1 := by simp [sgn]
  have key := card_tail_le (m := 2 * a) sgn hg h0 h1 hsum hsq (2 * D)
  have hsub : univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)
      ⊆ tail (m := 2 * a) sgn (2 * D) := by
    intro β hβ
    simp only [mem_filter, mem_univ, true_and] at hβ
    simp only [tail, mem_filter, mem_univ, true_and]
    rw [sum_sgn]
    have : ((a + D : ℕ) : ℝ) ≤ (ones β).card := by exact_mod_cast hβ
    push_cast at this; linarith
  calc ((univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)).card : ℝ)
      ≤ ((tail (m := 2 * a) sgn (2 * D)).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ (Fintype.card Bool : ℝ) ^ (2 * a)
          * Real.exp ((2 * a : ℕ) * (lam * 0 + lam ^ 2 * 1) - lam * (2 * D)) := key
    _ = 2 ^ (2 * a) * Real.exp (-((D : ℝ) ^ 2 / (2 * a))) := by
        rw [Fintype.card_bool]
        congr 2
        rw [hlam]; push_cast; field_simp; ring

/-- Lower tail, by complementing. -/
lemma card_low_le (D : ℕ) (ha : 0 < a) (hD : D ≤ 2 * a) :
    ((univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)).card : ℝ)
      ≤ 2 ^ (2 * a) * Real.exp (-((D : ℝ) ^ 2 / (2 * a))) := by
  classical
  refine le_trans ?_ (card_high_le D ha hD)
  have : (univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)).card
      ≤ (univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)).card := by
    refine card_le_card_of_injOn neg ?_ ?_
    · intro β hβ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hβ ⊢
      rw [ones_neg_card]; omega
    · intro β _ γ _ h
      funext i
      have := congrFun h i
      simpa [neg] using this
  exact_mod_cast this

end Tails

/-! ### One slice `β'' = const` -/

/-- Agreement on one slice: outside the window we pay the tails, inside offset Smolensky. -/
lemma slice_bound {a d h c θ u D : ℕ} (hh : 0 < h) (hθ : h ≤ θ) (hdiv : (c + θ) % h = 0)
    (hlo : a ≤ θ + u) (hhi : θ ≤ a + u) (hD : D + u ≤ h)
    {Q : (Fin (2 * a) → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    (univ.filter (fun β => Q β = bitAt h c (ones β).card)).card
      ≤ (univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)).card
        + (univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)).card
        + (univ.filter (fun M : Finset (Fin (2 * a)) => M.card ≤ a + u + d)).card := by
  classical
  set σ : ZMod 2 := if (c + θ) / h % 2 = 1 then 0 else 1
  set W := univ.filter (fun β : Fin (2 * a) → Bool => Q β = σ + THg θ β)
  have hsub : univ.filter (fun β => Q β = bitAt h c (ones β).card)
      ⊆ (univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)
        ∪ univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)) ∪ W := by
    intro β hβ
    simp only [mem_filter, mem_univ, true_and] at hβ
    simp only [mem_union, mem_filter, mem_univ, true_and, W]
    by_cases h1 : (ones β).card + D ≤ a
    · exact Or.inl (Or.inl h1)
    by_cases h2 : a + D ≤ (ones β).card
    · exact Or.inl (Or.inr h2)
    right
    rw [hβ, bitAt_window hθ hdiv (by omega) (by omega)]
    rfl
  have hW : W.card ≤ (univ.filter (fun M : Finset (Fin (2 * a)) =>
      M.card ≤ max (θ - 1) (2 * a - θ) + d)).card := by
    by_cases hs : (c + θ) / h % 2 = 1
    · have : W = univ.filter (fun β : Fin (2 * a) → Bool => Q β = THg θ β) := by
        ext β; simp [W, σ, hs]
      rw [this]; exact smolensky_gen θ hQ
    · have : W = univ.filter (fun β : Fin (2 * a) → Bool => Q β = 1 + THg θ β) := by
        ext β; simp [W, σ, hs]
      rw [this]; exact smolensky_gen_compl θ hQ
  have hM : (univ.filter (fun M : Finset (Fin (2 * a)) =>
      M.card ≤ max (θ - 1) (2 * a - θ) + d)).card
      ≤ (univ.filter (fun M : Finset (Fin (2 * a)) => M.card ≤ a + u + d)).card := by
    apply card_le_card
    intro M hM
    simp only [mem_filter, mem_univ, true_and] at hM ⊢
    have : max (θ - 1) (2 * a - θ) ≤ a + u := by omega
    omega
  calc _ ≤ ((univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)
        ∪ univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)) ∪ W).card :=
        card_le_card hsub
    _ ≤ (univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a)
        ∪ univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card)).card + W.card :=
        card_union_le _ _
    _ ≤ _ := by
        have := card_union_le (univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + D ≤ a))
          (univ.filter (fun β : Fin (2 * a) → Bool => a + D ≤ (ones β).card))
        omega

/-- The per-residue bound `G(v)`, `v = (c + a + g) mod h`. -/
def Gr (a g h d : ℕ) (v : ℕ) : ℝ :=
  if v ≤ 2 * g then
    min 1 (2 * Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a))) + 1 / 2
      + (((v - g : ℕ) + (g - v : ℕ) : ℕ) + d + 1 / 2) * (((2 * a).choose a : ℝ) / 4 ^ a))
  else 1

lemma Gr_nonneg (a g h d v : ℕ) : 0 ≤ Gr a g h d v := by
  unfold Gr; split_ifs
  · apply le_min zero_le_one; positivity
  · exact zero_le_one

lemma Gr_le_one (a g h d v : ℕ) : Gr a g h d v ≤ 1 := by
  unfold Gr; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- **One slice, real form.** -/
lemma slice_real {a g h d c : ℕ} (hh : 0 < h) (hg : 2 * g < h) (ha : h + 2 * g ≤ a)
    (hD : h - g ≤ 2 * a) {Q : (Fin (2 * a) → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    ((univ.filter (fun β => Q β = bitAt h c (ones β).card)).card : ℝ)
      ≤ 2 ^ (2 * a) * Gr a g h d ((c + a + g) % h) := by
  classical
  have h2a : ((univ : Finset (Fin (2 * a) → Bool)).card : ℝ) = 2 ^ (2 * a) := by
    simp [card_univ]
  have htriv : ((univ.filter (fun β => Q β = bitAt h c (ones β).card)).card : ℝ)
      ≤ 2 ^ (2 * a) := by
    rw [← h2a]; exact_mod_cast card_le_card (filter_subset _ _)
  set v := (c + a + g) % h with hv
  unfold Gr
  split_ifs with hv2
  · rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
    refine le_min htriv ?_
    set u := (v - g) + (g - v)
    have hvh : v < h := Nat.mod_lt _ hh
    have hdiv : (c + (a + g - v)) % h = 0 := by
      have e := Nat.div_add_mod (c + a + g) h
      have : c + (a + g - v) = h * ((c + a + g) / h) := by omega
      rw [this, Nat.mul_mod_right]
    have hb := slice_bound (a := a) (d := d) (u := u) (D := h - g) hh (by omega) hdiv
      (by omega) (by omega) (by omega) hQ
    have hapos : 0 < a := by omega
    have t1 := card_low_le (a := a) (h - g) hapos hD
    have t2 := card_high_le (a := a) (h - g) hapos hD
    have t3 := two_mul_card_low_le (F := 2 * a) (u + d)
    have e2 : 2 * a / 2 = a := by omega
    rw [e2] at t3
    have t3' : 2 * ((univ.filter (fun M : Finset (Fin (2 * a)) => M.card ≤ a + u + d)).card : ℝ)
        ≤ 2 ^ (2 * a) + (2 * (u + d) + 1) * ((2 * a).choose a : ℝ) := by
      rw [show a + u + d = a + (u + d) by ring]; exact_mod_cast t3
    have hb' : ((univ.filter (fun β => Q β = bitAt h c (ones β).card)).card : ℝ)
        ≤ ((univ.filter (fun β : Fin (2 * a) → Bool => (ones β).card + (h - g) ≤ a)).card : ℝ)
          + ((univ.filter (fun β : Fin (2 * a) → Bool => a + (h - g) ≤ (ones β).card)).card : ℝ)
          + ((univ.filter (fun M : Finset (Fin (2 * a)) => M.card ≤ a + u + d)).card : ℝ) := by
      exact_mod_cast hb
    have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
    have hpos : (0 : ℝ) < 2 ^ (2 * a) := by positivity
    rw [h4]
    have : (2 : ℝ) ^ (2 * a) * (2 * Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a))) + 1 / 2
        + ((u : ℕ) + d + 1 / 2) * (((2 * a).choose a : ℝ) / 2 ^ (2 * a)))
        = 2 * (2 ^ (2 * a) * Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a))))
          + (2 ^ (2 * a) + (2 * (u + d) + 1) * ((2 * a).choose a : ℝ)) / 2 := by
      field_simp; ring
    rw [this]
    linarith
  · rw [mul_one]; exact htriv

/-! ### Averaging over `|β''| ~ Bin(N)` -/

section Average

/-- `C(N,k) ≤ C(N,k+1)` below the middle, `≥` above. -/
lemma choose_rise {N k : ℕ} (hk : k + 1 ≤ N / 2) : N.choose k ≤ N.choose (k + 1) := by
  have e := Nat.choose_succ_right_eq N k
  have : k + 1 ≤ N - k := by omega
  have h1 : N.choose k * (k + 1) ≤ N.choose (k + 1) * (k + 1) := by
    rw [e]; exact Nat.mul_le_mul_left _ this
  exact Nat.le_of_mul_le_mul_right h1 (by omega)

lemma choose_fall {N k : ℕ} (hk : N / 2 ≤ k) : N.choose (k + 1) ≤ N.choose k := by
  have e := Nat.choose_succ_right_eq N k
  have : N - k ≤ k + 1 := by omega
  have h1 : N.choose (k + 1) * (k + 1) ≤ N.choose k * (k + 1) := by
    rw [e]; exact Nat.mul_le_mul_left _ this
  exact Nat.le_of_mul_le_mul_right h1 (by omega)

/-- Total positive variation of the binomial row is its maximum. -/
lemma pos_var_le (N : ℕ) : ∀ n, (N.choose 0 : ℝ)
    + ∑ j ∈ range n, max 0 ((N.choose (j + 1) : ℝ) - N.choose j) ≤ N.choose (min n (N / 2)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc]
    by_cases hn : n + 1 ≤ N / 2
    · have hr : (N.choose n : ℝ) ≤ N.choose (n + 1) := by exact_mod_cast choose_rise hn
      rw [max_eq_right (by linarith), min_eq_left hn]
      rw [min_eq_left (by omega)] at ih
      linarith
    · have hf : (N.choose (n + 1) : ℝ) ≤ N.choose n := by exact_mod_cast choose_fall (by omega)
      rw [max_eq_left (by linarith), add_zero, min_eq_right (by omega)]
      rw [min_eq_right (by omega)] at ih
      exact ih

/-- Shifting a `[0,1]`-valued function by one changes its binomial average by `≤ C(N,N/2)`. -/
lemma shift_one (N : ℕ) (H : ℕ → ℝ) (h0 : ∀ j, 0 ≤ H j) (h1 : ∀ j, H j ≤ 1) :
    ∑ j ∈ range (N + 1), (N.choose j : ℝ) * H j
      ≤ ∑ j ∈ range (N + 1), (N.choose j : ℝ) * H (j + 1) + N.choose (N / 2) := by
  -- T n := ∑_{j<n+1} x_j H j - ∑_{j<n} x_j H (j+1) ≤ x_0 + ∑_{j<n} (x_{j+1}-x_j)⁺
  have key : ∀ n, ∑ j ∈ range (n + 1), (N.choose j : ℝ) * H j
      - ∑ j ∈ range n, (N.choose j : ℝ) * H (j + 1)
      ≤ (N.choose 0 : ℝ) + ∑ j ∈ range n, max 0 ((N.choose (j + 1) : ℝ) - N.choose j) := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, sum_range_one, range_zero, sum_empty, sub_zero, add_zero]
      have := h1 0
      have : (0 : ℝ) ≤ N.choose 0 := Nat.cast_nonneg _
      nlinarith [h0 0]
    | succ n ih =>
      simp only [sum_range_succ] at ih ⊢
      have hm : ((N.choose (n + 1) : ℝ) - N.choose n) * H (n + 1)
          ≤ max 0 ((N.choose (n + 1) : ℝ) - N.choose n) := by
        rcases le_or_gt 0 ((N.choose (n + 1) : ℝ) - N.choose n) with hp | hp
        · rw [max_eq_right hp]; nlinarith [h1 (n + 1)]
        · rw [max_eq_left hp.le]; nlinarith [h0 (n + 1)]
      linarith
  have hk := key N
  have hv := pos_var_le N N
  rw [min_eq_right (Nat.div_le_self _ _)] at hv
  rw [sum_range_succ (fun j => (N.choose j : ℝ) * H (j + 1))]
  have : 0 ≤ (N.choose N : ℝ) * H (N + 1) := mul_nonneg (Nat.cast_nonneg _) (h0 _)
  linarith

/-- Sum of an `h`-periodic function over any window of length `h`. -/
lemma sum_rot (h : ℕ) (G : ℕ → ℝ) : ∀ e, ∑ s ∈ range h, G ((e + s) % h) = ∑ v ∈ range h, G v := by
  intro e
  induction e with
  | zero =>
    refine sum_congr rfl (fun s hs => ?_)
    rw [zero_add, Nat.mod_eq_of_lt (mem_range.mp hs)]
  | succ e ih =>
    rw [← ih]
    have h1 := sum_range_succ' (fun s => G ((e + s) % h)) h
    have h2 := sum_range_succ (fun s => G ((e + s) % h)) h
    simp only [add_zero, Nat.add_mod_right] at h1 h2
    have : ∑ s ∈ range h, G ((e + 1 + s) % h) = ∑ s ∈ range h, G ((e + (s + 1)) % h) := by
      refine sum_congr rfl (fun s _ => ?_); congr 2; ring
    rw [this]
    linarith

/-- **Binomial averaging.** For `G : ℕ → [0,1]`,
`∑_j C(N,j) G((c+j) mod h) ≤ (2^N/h) ∑_{v<h} G v + h · C(N,N/2) / 2`. -/
theorem binom_avg (N h : ℕ) (hh : 0 < h) (G : ℕ → ℝ) (h0 : ∀ v, 0 ≤ G v) (h1 : ∀ v, G v ≤ 1)
    (c : ℕ) :
    ∑ j ∈ range (N + 1), (N.choose j : ℝ) * G ((c + j) % h)
      ≤ 2 ^ N / h * ∑ v ∈ range h, G v + h * (N.choose (N / 2) : ℝ) / 2 := by
  set Φ : ℕ → ℝ := fun s => ∑ j ∈ range (N + 1), (N.choose j : ℝ) * G ((c + j + s) % h)
  set C : ℝ := ((N.choose (N / 2) : ℕ) : ℝ)
  have hstep : ∀ s, Φ s ≤ Φ (s + 1) + C := by
    intro s
    have := shift_one N (fun j => G ((c + j + s) % h)) (fun j => h0 _) (fun j => h1 _)
    have e : Φ (s + 1) = ∑ j ∈ range (N + 1), (N.choose j : ℝ) * G ((c + (j + 1) + s) % h) := by
      simp only [Φ]
      refine sum_congr rfl (fun j _ => ?_)
      rw [show c + (j + 1) + s = c + j + (s + 1) by ring]
    rw [e]; exact this
  have hs : ∀ s, Φ 0 ≤ Φ s + s * C := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => have := hstep s; push_cast; linarith
  have hsum : ∑ s ∈ range h, Φ s = 2 ^ N * ∑ v ∈ range h, G v := by
    simp only [Φ]
    rw [sum_comm]
    have : ∀ j ∈ range (N + 1), ∑ s ∈ range h, (N.choose j : ℝ) * G ((c + j + s) % h)
        = (N.choose j : ℝ) * ∑ v ∈ range h, G v := by
      intro j _
      rw [← mul_sum, sum_rot h G (c + j)]
    rw [sum_congr rfl this, ← sum_mul]
    congr 1
    have := Nat.sum_range_choose N
    exact_mod_cast this
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have htot : (h : ℝ) * Φ 0 ≤ 2 ^ N * ∑ v ∈ range h, G v + C * ((h : ℝ) * h / 2) := by
    have hle : ∑ s ∈ range h, Φ 0 ≤ ∑ s ∈ range h, (Φ s + s * C) :=
      sum_le_sum (fun s _ => hs s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, hsum, ← sum_mul] at hle
    have hid : (∑ s ∈ range h, (s : ℝ)) * 2 = h * ((h - 1 : ℕ) : ℝ) := by
      have := sum_range_id_mul_two h
      have h' : ((∑ i ∈ range h, i : ℕ) : ℝ) * 2 = ((h * (h - 1) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast [Nat.cast_sum] at h'
      rw [h']
    have hh1 : ((h - 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.sub_le h 1
    have : (∑ s ∈ range h, (s : ℝ)) ≤ (h : ℝ) * h / 2 := by
      have : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      nlinarith
    nlinarith
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hΦ : Φ 0 = ∑ j ∈ range (N + 1), (N.choose j : ℝ) * G ((c + j) % h) := by
    simp [Φ]
  rw [← hΦ]
  rw [div_mul_eq_mul_div, ← sub_nonneg]
  have : Φ 0 ≤ (2 ^ N * ∑ v ∈ range h, G v) / h + h * C / 2 := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith
  linarith

end Average

/-! ### Counting by weight -/

lemma sum_by_weight (N : ℕ) (f : ℕ → ℝ) :
    ∑ β : Fin N → Bool, f (ones β).card = ∑ j ∈ range (N + 1), (N.choose j : ℝ) * f j := by
  classical
  let e : (Fin N → Bool) ≃ Finset (Fin N) :=
    { toFun := ones
      invFun := ind
      left_inv := fun β => by funext i; simp [ones, ind]
      right_inv := fun M => by ext i; simp [ones, ind] }
  have h1 : ∑ β : Fin N → Bool, f (ones β).card = ∑ M : Finset (Fin N), f M.card :=
    Fintype.sum_equiv e _ _ (fun β => rfl)
  rw [h1]
  have h2 := Finset.sum_powerset_apply_card f (x := (univ : Finset (Fin N)))
  rw [powerset_univ, card_univ, Fintype.card_fin] at h2
  rw [h2]
  simp [nsmul_eq_mul]

/-! ### The pair form -/

/-- Sum of `|v - g|` over `v < 2g+1`. -/
lemma sum_absdev (g : ℕ) :
    ∑ v ∈ range (2 * g + 1), ((v - g : ℕ) + (g - v : ℕ)) = g * (g + 1) := by
  have L1 : ∀ n, 2 * ∑ v ∈ range n, (v - g) = (n - g) * (n - g - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add, ih]
      rcases le_or_gt g n with hn | hn
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
        have e1 : g + t + 1 - g = t + 1 := by omega
        have e2 : g + t - g = t := by omega
        rw [e1, e2]
        rcases t with _ | t
        · simp
        · simp only [Nat.add_sub_cancel]; ring
      · have e1 : n + 1 - g = 0 := by omega
        have e2 : n - g = 0 := by omega
        simp [e1, e2]
  have L2 : ∀ n, 2 * ∑ v ∈ range n, (g - v) + (g - n) * (g - n + 1) = g * (g + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, mul_add]
      rcases le_or_gt g n with hn | hn
      · have e1 : g - (n + 1) = 0 := by omega
        have e2 : g - n = 0 := by omega
        rw [e1, e2]; rw [e2] at ih; simpa using ih
      · obtain ⟨t, ht⟩ : ∃ t, g = n + 1 + t := ⟨g - (n + 1), by omega⟩
        have e1 : g - (n + 1) = t := by omega
        have e2 : g - n = t + 1 := by omega
        rw [e2] at ih; rw [e1, e2]
        nlinarith [ih]
  have a1 := L1 (2 * g + 1)
  have a2 := L2 (2 * g + 1)
  rw [show 2 * g + 1 - g = g + 1 by omega, show g + 1 - 1 = g by omega] at a1
  rw [show g - (2 * g + 1) = 0 by omega, zero_mul, add_zero] at a2
  rw [sum_add_distrib]
  nlinarith

/-- Mean of `G` over residues. -/
lemma sum_Gr_le {a g h d : ℕ} (hg : 2 * g + 1 ≤ h) :
    ∑ v ∈ range h, Gr a g h d v
      ≤ (2 * g + 1) * (2 * Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a))) + 1 / 2
          + (d + 1 / 2) * (((2 * a).choose a : ℝ) / 4 ^ a))
        + (((2 * a).choose a : ℝ) / 4 ^ a) * (g * (g + 1)) + (h - (2 * g + 1)) := by
  set E := 2 * Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a)))
  set p := (((2 * a).choose a : ℝ) / 4 ^ a)
  have hp : 0 ≤ p := by positivity
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (2 * g + 1)) hg]
  have hA : ∑ v ∈ Ico 0 (2 * g + 1), Gr a g h d v
      ≤ ∑ v ∈ range (2 * g + 1), (E + 1 / 2 + (d + 1 / 2) * p
          + p * (((v - g : ℕ) + (g - v : ℕ) : ℕ) : ℝ)) := by
    rw [← range_eq_Ico]
    refine sum_le_sum (fun v hv => ?_)
    have hv' : v ≤ 2 * g := by have := mem_range.mp hv; omega
    unfold Gr
    rw [if_pos hv']
    refine le_trans (min_le_right _ _) (le_of_eq ?_)
    simp only [E, p]; push_cast; ring
  have hB : ∑ v ∈ Ico (2 * g + 1) h, Gr a g h d v ≤ (h - (2 * g + 1) : ℝ) := by
    calc ∑ v ∈ Ico (2 * g + 1) h, Gr a g h d v ≤ ∑ v ∈ Ico (2 * g + 1) h, (1 : ℝ) :=
          sum_le_sum (fun v _ => Gr_le_one _ _ _ _ _)
      _ = (h - (2 * g + 1) : ℝ) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hg]; push_cast; ring
  have hS : ∑ v ∈ range (2 * g + 1), (E + 1 / 2 + (d + 1 / 2) * p
          + p * (((v - g : ℕ) + (g - v : ℕ) : ℕ) : ℝ))
      = (2 * g + 1) * (E + 1 / 2 + (d + 1 / 2) * p) + p * (g * (g + 1)) := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    have := sum_absdev g
    have h' : (∑ v ∈ range (2 * g + 1), (((v - g : ℕ) + (g - v : ℕ) : ℕ) : ℝ))
        = (g : ℝ) * (g + 1) := by exact_mod_cast this
    rw [h']; push_cast; ring
  linarith

/-- **Lemma PS, pair form.** -/
theorem ps_pair {a N h g d : ℕ} (K : ℕ) (hh : 0 < h) (hg : 2 * g < h) (ha : h + 2 * g ≤ a)
    (hD : h - g ≤ 2 * a)
    (Q : (Fin (2 * a) → Bool) → (Fin N → Bool) → ZMod 2)
    (hQ : ∀ β'', (fun β' => Q β' β'') ∈ V d) :
    ((univ.filter (fun p : (Fin (2 * a) → Bool) × (Fin N → Bool) =>
        Q p.1 p.2 = bitAt h K ((ones p.1).card + (ones p.2).card))).card : ℝ)
      ≤ 2 ^ (2 * a) * (2 ^ N / h * ∑ v ∈ range h, Gr a g h d v
          + h * (N.choose (N / 2) : ℝ) / 2) := by
  classical
  have hsplit : ((univ.filter (fun p : (Fin (2 * a) → Bool) × (Fin N → Bool) =>
        Q p.1 p.2 = bitAt h K ((ones p.1).card + (ones p.2).card))).card : ℝ)
      = ∑ β'' : Fin N → Bool, ((univ.filter (fun β' : Fin (2 * a) → Bool =>
          Q β' β'' = bitAt h (K + (ones β'').card) (ones β').card)).card : ℝ) := by
    rw [card_filter, Nat.cast_sum, Fintype.sum_prod_type_right]
    refine sum_congr rfl (fun β'' _ => ?_)
    rw [card_filter, Nat.cast_sum]
    refine sum_congr rfl (fun β' _ => ?_)
    have : bitAt h K ((ones β').card + (ones β'').card)
        = bitAt h (K + (ones β'').card) (ones β').card := by
      unfold bitAt; rw [add_assoc, add_comm (ones β').card]
    rw [this]
  rw [hsplit]
  calc ∑ β'' : Fin N → Bool, ((univ.filter (fun β' : Fin (2 * a) → Bool =>
          Q β' β'' = bitAt h (K + (ones β'').card) (ones β').card)).card : ℝ)
      ≤ ∑ β'' : Fin N → Bool, 2 ^ (2 * a) * Gr a g h d (((K + a + g) + (ones β'').card) % h) := by
        refine sum_le_sum (fun β'' _ => ?_)
        have := slice_real (c := K + (ones β'').card) hh hg ha hD (hQ β'')
        rw [show K + a + g + (ones β'').card = K + (ones β'').card + a + g by ring]
        exact this
    _ = 2 ^ (2 * a) * ∑ j ∈ range (N + 1), (N.choose j : ℝ)
          * Gr a g h d ((K + a + g + j) % h) := by
        rw [← mul_sum, sum_by_weight N (fun j => Gr a g h d ((K + a + g + j) % h))]
    _ ≤ _ := by
        gcongr
        exact binom_avg N h hh _ (Gr_nonneg a g h d) (Gr_le_one a g h d) _

/-! ### Back to one cube `{0,1}^(2a+N)` -/

section Cube

variable {A N : ℕ}

/-- `(β', β'') ↦ β' ++ β''`. -/
def appendE (A N : ℕ) : (Fin A → Bool) × (Fin N → Bool) ≃ (Fin (A + N) → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun β := (fun i => β (Fin.castAdd N i), fun j => β (Fin.natAdd A j))
  left_inv p := by ext i <;> simp
  right_inv β := Fin.append_castAdd_natAdd

lemma ones_append (β' : Fin A → Bool) (β'' : Fin N → Bool) :
    (ones (Fin.append β' β'')).card = (ones β').card + (ones β'').card := by
  unfold ones
  rw [card_filter, card_filter, card_filter, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Fixing `β''` keeps the degree. -/
lemma append_mem {d : ℕ} {Q : (Fin (A + N) → Bool) → ZMod 2} (hQ : Q ∈ V d)
    (β'' : Fin N → Bool) : (fun β' => Q (Fin.append β' β'')) ∈ V (F := A) d := by
  classical
  set P : Finset (Fin (A + N)) := univ.filter (fun i => (i : ℕ) < A)
  have hP : ∀ i : Fin A, Fin.castAdd N i ∈ P := fun i => by simp [P]
  let e : Fin A ≃ P := Equiv.ofBijective (fun i => ⟨Fin.castAdd N i, hP i⟩)
    ⟨fun i j h => by
      have := congrArg (fun x : P => ((x : Fin (A + N)) : ℕ)) h
      exact Fin.ext (by simpa using this),
     fun ⟨x, hx⟩ => by
      simp only [P, mem_filter, mem_univ, true_and] at hx
      exact ⟨⟨x, hx⟩, Subtype.ext (Fin.ext rfl)⟩⟩
  have key : (fun β' => Q (Fin.append β' β''))
      = fun β' => Q (embed P e (Fin.append (fun _ => false) β'') β') := by
    funext β'
    congr 1
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · unfold embed
      rw [dif_pos (hP i)]
      have : e.symm ⟨Fin.castAdd N i, hP i⟩ = i := by
        rw [Equiv.symm_apply_eq]; rfl
      rw [this, Fin.append_left]
    · unfold embed
      have hj : Fin.natAdd A j ∉ P := by simp [P]
      rw [dif_neg hj, Fin.append_right, Fin.append_right]
  rw [key]
  exact restrict_mem P e _ hQ

lemma card_cube_eq (h K : ℕ) (Q : (Fin (A + N) → Bool) → ZMod 2) :
    (univ.filter (fun β => Q β = bitAt h K (ones β).card)).card
      = (univ.filter (fun p : (Fin A → Bool) × (Fin N → Bool) =>
          Q (Fin.append p.1 p.2) = bitAt h K ((ones p.1).card + (ones p.2).card))).card := by
  classical
  refine card_nbij' (appendE A N).symm (appendE A N) ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hβ ⊢
    have e1 : Fin.append ((appendE A N).symm β).1 ((appendE A N).symm β).2 = β :=
      (appendE A N).apply_symm_apply β
    rw [← ones_append, e1]; exact hβ
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    show Q (Fin.append p.1 p.2) = bitAt h K (ones (Fin.append p.1 p.2)).card
    rw [ones_append]; exact hp
  · intro β _; exact (appendE A N).apply_symm_apply β
  · intro p _; exact (appendE A N).symm_apply_apply p

end Cube

/-! ### Lemma PS with explicit constants -/

lemma exp_neg_four_le : Real.exp (-4) ≤ 1 / 54 := by
  have h1 := Real.exp_one_gt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have : (54 : ℝ) ≤ Real.exp 4 := by
    rw [h4]
    have : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1.le 4
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) this

/-- **Lemma PS (periodic Smolensky), Lean form.** Let `h ≥ 1024`, `200(d+1) ≤ h` and
`F ≥ 2600 h²`. Every `Q : {0,1}^F → F₂` of degree `≤ d` agrees with `⌊(K+|β|)/h⌋ mod 2` on at
most `93%` of the cube. -/
theorem periodic_smolensky {F d h : ℕ} (hh : 1024 ≤ h) (hd : 200 * (d + 1) ≤ h)
    (hF : 2600 * h ^ 2 ≤ F) (K : ℕ) {Q : (Fin F → Bool) → ZMod 2} (hQ : Q ∈ V d) :
    ((univ.filter (fun β => Q β = bitAt h K (ones β).card)).card : ℝ) ≤ 93 / 100 * 2 ^ F := by
  classical
  set H := h ^ 2 with hHdef
  have hH : 1024 * h ≤ H := by rw [hHdef, sq]; exact Nat.mul_le_mul_right h hh
  set a := H / 13 with hadef
  set g := h / 5 with hgdef
  have ha13 : 13 * a ≤ H := Nat.mul_div_le H 13
  have ha13' : H < 13 * a + 13 := by omega
  obtain ⟨N, rfl⟩ : ∃ N, F = 2 * a + N := ⟨F - 2 * a, by omega⟩
  have hN : 2500 * H ≤ N := by omega
  -- the pair form
  have hpair := ps_pair (a := a) (N := N) (h := h) (g := g) (d := d) K (by omega) (by omega)
    (by omega) (by omega) (fun p1 p2 => Q (Fin.append p1 p2)) (fun β'' => append_mem hQ β'')
  rw [card_cube_eq h K Q]
  refine le_trans hpair ?_
  have hS := sum_Gr_le (a := a) (g := g) (h := h) (d := d) (by omega)
  -- real parameters
  set E := Real.exp (-(((h - g : ℕ) : ℝ) ^ 2 / (2 * a))) with hE
  set p := (((2 * a).choose a : ℝ) / 4 ^ a) with hp
  set S := ∑ v ∈ range h, Gr a g h d v
  set C := ((N.choose (N / 2) : ℕ) : ℝ)
  have hr : (1024 : ℝ) ≤ h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) < h := by linarith
  have hapos : (0 : ℝ) < a := by
    have : 0 < a := by omega
    exact_mod_cast this
  -- (i) E ≤ 1/54
  have hE54 : E ≤ 1 / 54 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_four_le
    have h1 : 4 * h ≤ 5 * (h - g) := by omega
    have h1' : (4 : ℝ) * h ≤ 5 * ((h - g : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (13 : ℝ) * a ≤ (h : ℝ) ^ 2 := by
      have : ((13 * a : ℕ) : ℝ) ≤ ((h ^ 2 : ℕ) : ℝ) := by exact_mod_cast ha13
      push_cast at this; exact this
    have h3 : (8 : ℝ) * a ≤ ((h - g : ℕ) : ℝ) ^ 2 := by nlinarith
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith
  -- (ii) p · h ≤ 21/10
  have hp0 : 0 ≤ p := by positivity
  have hph : p * h ≤ 21 / 10 := by
    have hc := centralBinom_sq_mul_le a
    rw [Nat.centralBinom_eq_two_mul_choose] at hc
    have hc' : ((2 * a).choose a : ℝ) ^ 2 * (3 * a + 1) ≤ ((4 : ℝ) ^ a) ^ 2 := by
      have : (((2 * a).choose a ^ 2 * (3 * a + 1) : ℕ) : ℝ) ≤ ((16 ^ a : ℕ) : ℝ) := by
        exact_mod_cast hc
      push_cast at this
      rw [← pow_mul, mul_comm a 2, pow_mul]; norm_num; exact this
    have h4 : (0 : ℝ) < 4 ^ a := by positivity
    have hp2 : p ^ 2 * (3 * a + 1) ≤ 1 := by
      rw [hp, div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]; exact hc'
    have hH' : (h : ℝ) ^ 2 < 13 * a + 13 := by
      have : ((h ^ 2 : ℕ) : ℝ) < ((13 * a + 13 : ℕ) : ℝ) := by exact_mod_cast ha13'
      push_cast at this; exact this
    have ha' : (1000 : ℝ) ≤ a := by
      have : 1000 ≤ a := by omega
      exact_mod_cast this
    have : (p * h) ^ 2 ≤ (21 / 10) ^ 2 := by
      rw [mul_pow]
      have : (h : ℝ) ^ 2 ≤ (21 / 10) ^ 2 * (3 * a + 1) := by nlinarith
      calc p ^ 2 * (h : ℝ) ^ 2 ≤ p ^ 2 * ((21 / 10) ^ 2 * (3 * a + 1)) := by gcongr
        _ = (21 / 10) ^ 2 * (p ^ 2 * (3 * a + 1)) := by ring
        _ ≤ (21 / 10) ^ 2 * 1 := by gcongr
        _ = (21 / 10) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp this
  -- (iii)–(v) small facts
  have hx1 : (399 : ℝ) * h ≤ 1000 * (2 * g + 1) := by
    have : 399 * h ≤ 1000 * (2 * g + 1) := by omega
    exact_mod_cast this
  have hx2 : (2 * g + 1 : ℝ) ≤ h := by
    have : 2 * g + 1 ≤ h := by omega
    exact_mod_cast this
  have hdh : (200 : ℝ) * (d + 1) ≤ h := by exact_mod_cast hd
  have hg5 : (5 : ℝ) * g ≤ h := by
    have : 5 * g ≤ h := by omega
    exact_mod_cast this
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  -- Y = 2E + (d+½)p ≤ 1/20
  have hY : 2 * E + (d + 1 / 2) * p ≤ 1 / 20 := by
    have : (d + 1 / 2 : ℝ) * p ≤ 21 / 2000 := by
      have : (d + 1 / 2 : ℝ) * p ≤ (h / 200) * p := by
        gcongr; linarith
      calc (d + 1 / 2 : ℝ) * p ≤ (h / 200) * p := this
        _ = p * h / 200 := by ring
        _ ≤ 21 / 10 / 200 := by gcongr
        _ = 21 / 2000 := by norm_num
    linarith
  -- p g (g+1) ≤ 0.0845 h
  have hpg : p * (g * (g + 1)) ≤ 845 / 10000 * h := by
    have : p * (g * (g + 1)) ≤ p * ((h / 5) * (h / 5 + 1)) := by
      gcongr <;> linarith
    have e : p * ((h / 5) * (h / 5 + 1)) = (p * h) * (h / 25 + 1 / 5) := by ring
    have : (p * h) * (h / 25 + 1 / 5) ≤ 21 / 10 * (h / 25 + 1 / 5) := by
      gcongr
    nlinarith
  -- S ≤ 0.91 h
  have hS' : S ≤ 91 / 100 * h := by
    have hS0 : S ≤ (2 * g + 1) * (1 / 2 + (2 * E + (d + 1 / 2) * p)) + p * (g * (g + 1))
        + (h - (2 * g + 1)) := by
      have := hS; linarith
    have hx0 : (0 : ℝ) ≤ 2 * g + 1 := by positivity
    have : (2 * g + 1 : ℝ) * (1 / 2 + (2 * E + (d + 1 / 2) * p))
        ≤ (2 * g + 1) * (1 / 2 + 1 / 20) := by gcongr
    nlinarith
  -- the shift error: 50 h C ≤ 2^N
  have hC : (50 : ℝ) * h * C ≤ 2 ^ N := by
    have hc := choose_half_sq_mul_le N
    have hn : (50 * h * N.choose (N / 2)) ^ 2 ≤ (2 ^ N) ^ 2 := by
      have e : (50 * h * N.choose (N / 2)) ^ 2 = 2500 * H * (N.choose (N / 2)) ^ 2 := by
        rw [hHdef]; ring
      rw [e, ← pow_mul, mul_comm N 2, pow_mul]
      norm_num
      calc 2500 * H * N.choose (N / 2) ^ 2 ≤ N * N.choose (N / 2) ^ 2 :=
            Nat.mul_le_mul_right _ hN
        _ = N.choose (N / 2) ^ 2 * N := by ring
        _ ≤ 4 ^ N := hc
    have hn' : 50 * h * N.choose (N / 2) ≤ 2 ^ N :=
      (Nat.pow_le_pow_iff_left (by norm_num)).mp hn
    have : (((50 * h * N.choose (N / 2)) : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast hn'
    push_cast at this
    simp only [C]
    exact this
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have h2a : (0 : ℝ) < 2 ^ (2 * a) := by positivity
  rw [pow_add]
  have hS0 : 0 ≤ S := sum_nonneg (fun v _ => Gr_nonneg a g h d v)
  have : 2 ^ N / h * S ≤ 91 / 100 * 2 ^ N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr0]
    nlinarith
  have : (h : ℝ) * C / 2 ≤ 1 / 100 * 2 ^ N := by
    have : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    nlinarith
  have : 2 ^ N / h * S + h * C / 2 ≤ 93 / 100 * 2 ^ N := by linarith
  calc (2 : ℝ) ^ (2 * a) * (2 ^ N / h * S + h * C / 2)
      ≤ 2 ^ (2 * a) * (93 / 100 * 2 ^ N) := by gcongr
    _ = 93 / 100 * (2 ^ (2 * a) * 2 ^ N) := by ring

end Periodic

end

end ProblemQ
