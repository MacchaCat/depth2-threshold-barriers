import ProblemQ.NLBarrier

/-!
# Theorem NL-U at CTW's parameters

Chen–Tal–Wang take `k = n^{ε/10}` live variables, lists of size `ln L ≈ n^{ε/100}` and
`F₂`-degree `d ≈ n^{1-ε/6}`. We show, with exactly these growth rates, that `1hotSUM` list
templates fail on at least half of all circuits once `m ≥ 6000 · n^{5/2 - ε/3}` — just above CTW's
own range `m ≤ n^{5/2 - ε}`.

`nl_u_ctw`: for every `0 < ε < 1` there is `N₀` such that for all `n ≥ N₀`, with
`k = ⌈n^{ε/10}⌉`, `M = ⌈2 n^{ε/100}⌉ + 57`, every list of `L ≤ exp(n^{ε/100})` polynomials of
gate-degree `d ≤ n^{1-ε/6}` succeeds (error `δ ≤ 1/(100M)`) on some live set of size `k` for at
most half of all circuits with `m ≥ 6000 · n^{5/2 - ε/3}` gates.
-/

open Finset Filter Real

namespace ProblemQ

noncomputable section

namespace NLU

/-- Live variables at CTW scale. -/
def kC (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (ε / 10)⌉₊

/-- Frame size used for lists of size `exp(n^{ε/100})`. -/
def MC (ε : ℝ) (n : ℕ) : ℕ := ⌈2 * (n : ℝ) ^ (ε / 100)⌉₊ + 57

/-! ### Elementary numeric facts -/

lemma half_le_log_five_thirds : (1 / 2 : ℝ) ≤ Real.log (5 / 3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith

lemma two_pow_forty_le : (2 : ℝ) ^ 40 ≤ Real.exp 28 := by
  have h1 := Real.exp_one_gt_d9
  have h28 : Real.exp 28 = Real.exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h28]
  calc (2 : ℝ) ^ 40 ≤ (2.7182818283 : ℝ) ^ 28 := by norm_num
    _ ≤ Real.exp 1 ^ 28 := pow_le_pow_left₀ (by norm_num) h1.le 28

/-- `L (3/5)^M ≤ 2^{-40}` whenever `ln L ≤ t` and `M ≥ 2t + 57`. -/
lemma list_small {L M : ℕ} {t : ℝ} (hL : (L : ℝ) ≤ Real.exp t) (hM : 2 * t + 57 ≤ M) :
    (L : ℝ) * (3 / 5) ^ M ≤ 1 / 2 ^ 40 := by
  have h35 : ((3 : ℝ) / 5) ^ M = Real.exp (-(M * Real.log (5 / 3))) := by
    rw [show -((M : ℝ) * Real.log (5 / 3)) = (M : ℝ) * Real.log (3 / 5) by
      rw [show (3 : ℝ) / 5 = (5 / 3)⁻¹ by norm_num, Real.log_inv]; ring]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hlog := half_le_log_five_thirds
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have h1 : ((3 : ℝ) / 5) ^ M ≤ Real.exp (-(t + 28)) := by
    rw [h35]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h2 : (L : ℝ) * (3 / 5) ^ M ≤ Real.exp t * Real.exp (-(t + 28)) := by
    gcongr
  rw [← Real.exp_add, show t + -(t + 28) = -28 by ring, Real.exp_neg] at h2
  refine le_trans h2 ?_
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) two_pow_forty_le

/-! ### Asymptotic facts, eventually in `x → ∞` -/

/-- `c · x^p · log x ≤ x^q` eventually, for `p < q`, `c > 0`. -/
lemma ev_log_mul_rpow {p q c : ℝ} (hpq : p < q) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * x ^ p * Real.log x ≤ x ^ q := by
  have h := (isLittleO_log_rpow_atTop (sub_pos.mpr hpq)).bound (show (0 : ℝ) < 1 / c by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)] at hx
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
  calc c * x ^ p * Real.log x ≤ c * x ^ p * (1 / c * x ^ (q - p)) := by gcongr
    _ = x ^ p * x ^ (q - p) := by field_simp
    _ = x ^ q := by rw [← Real.rpow_add hx0]; ring_nf

/-- `C ≤ x^r` eventually, for `r > 0`. -/
lemma ev_const_le_rpow {r C : ℝ} (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, C ≤ x ^ r :=
  (tendsto_rpow_atTop hr).eventually_ge_atTop C

/-! ### The theorem -/

open Classical in
/-- **NL-U at CTW scale.** -/
theorem nl_u_ctw (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ {m L d : ℕ}
      (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → Fin (m + 1) → ZMod 2),
      (∀ a x s, (fun u => P a x u s) ∈ Smolensky.V d) →
      ∀ δ : ℝ, 0 ≤ δ → δ * MC ε n ≤ 1 / 100 →
      (L : ℝ) ≤ Real.exp ((n : ℝ) ^ (ε / 100)) →
      (d : ℝ) ≤ (n : ℝ) ^ (1 - ε / 6) →
      6000 * (n : ℝ) ^ (5 / 2 - ε / 3) ≤ m →
      ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
          ∃ I : Finset (Fin n), I.card = kC ε n ∧ Succeeds (hotP P) δ ω I)).card : ℝ)
        ≤ 1 / 2 * (Fintype.card (Gate n (Tset n)) : ℝ) ^ m := by
  set a := ε / 100 with ha
  set b := ε / 10 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hb1 : b < 1 := by rw [hb]; linarith
  -- eventual facts in x : ℝ
  have E1 : ∀ᶠ x : ℝ in atTop, 3456000 ≤ x ^ (7 * a) := ev_const_le_rpow (by positivity)
  have E2 : ∀ᶠ x : ℝ in atTop, 2 * x ^ b + 802 ≤ x ^ (1 : ℝ) := by
    have h1 := ev_log_mul_rpow (p := b) (q := 1) (c := 4) hb1 (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1604 : ℝ)]
      with x hx hxe hx2
    have hx0 : 0 < x := by linarith
    have hlog : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hxe
    have hxb : 0 ≤ x ^ b := (Real.rpow_pos_of_pos hx0 b).le
    rw [Real.rpow_one] at hx ⊢
    nlinarith
  have E3 : ∀ᶠ x : ℝ in atTop,
      (x ^ b + 1) * Real.log x + (2 * (x ^ b + 1) + 45) * Real.log 2 ≤ x * Real.log 2 := by
    have h1 := ev_log_mul_rpow (p := b) (q := 1) (c := 64) hb1 (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (200 : ℝ)]
      with x hx hxe hx200
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hl2' : 1 / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hb1x : 1 ≤ x ^ b := Real.one_le_rpow (by linarith) hb0.le
    rw [Real.rpow_one] at hx
    have hP : x ^ b * Real.log x ≤ x / 64 := by linarith
    have hlx : Real.log x ≤ x ^ b * Real.log x := by nlinarith
    have hxb : x ^ b ≤ x ^ b * Real.log x := by nlinarith
    have t1 : (2 * (x ^ b + 1) + 45) * Real.log 2 ≤ 2 * (x ^ b + 1) + 45 := by nlinarith
    have t2 : x / 2 ≤ x * Real.log 2 := by nlinarith
    nlinarith
  have E4 : ∀ᶠ x : ℝ in atTop,
      27 * (4 * Real.sqrt x + 5) * ((x ^ b + 1) * Real.log x + Real.log (2 * x ^ a + 58) + 5)
        ≤ 6000 * x ^ (5 / 2 - ε / 3) := by
    -- crude: everything ≤ 1000 * x^(0.5 + b + 0.1)... use log bounds
    have h1 := ev_log_mul_rpow (p := 1 / 2 + b) (q := 5 / 2 - ε / 3) (c := 27 * 9 * 8)
      (by rw [hb]; linarith) (by norm_num)
    filter_upwards [h1, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (100 : ℝ)]
      with x hx hxe hx100
    have hx0 : 0 < x := by linarith
    have hlog : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
    have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have hxb1 : 1 ≤ x ^ b := by apply Real.one_le_rpow <;> linarith
    have hxa1 : 1 ≤ x ^ a := by apply Real.one_le_rpow <;> linarith
    have hxab : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [ha, hb]; linarith)
    have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; linarith
    -- log (2 x^a + 58) ≤ log (60 x^b) ≤ log x^b ... bound by 60 * x^b ≤ 60 x^b * log x
    have hlogM : Real.log (2 * x ^ a + 58) ≤ 60 * x ^ b * Real.log x := by
      have hpos : 0 < 2 * x ^ a + 58 := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      nlinarith
    have hprod : x ^ (1 / 2 + b) = Real.sqrt x * x ^ b := by
      rw [Real.rpow_add hx0, hsq]
    have hA : (x ^ b + 1) * Real.log x + Real.log (2 * x ^ a + 58) + 5
        ≤ 8 * x ^ b * Real.log x * 9 := by nlinarith
    have hB : 27 * (4 * Real.sqrt x + 5) ≤ 27 * 9 * Real.sqrt x := by nlinarith
    calc 27 * (4 * Real.sqrt x + 5) * ((x ^ b + 1) * Real.log x + Real.log (2 * x ^ a + 58) + 5)
        ≤ (27 * 9 * Real.sqrt x) * (8 * x ^ b * Real.log x * 9) := by
          have hl0 : 0 ≤ Real.log x := by linarith
          have hl1 : 0 ≤ Real.log (2 * x ^ a + 58) := Real.log_nonneg (by linarith)
          apply mul_le_mul hB hA (by positivity) (by positivity)
      _ = 27 * 9 * 8 * x ^ (1 / 2 + b) * Real.log x * 9 := by rw [hprod]; ring
      _ ≤ x ^ (5 / 2 - ε / 3) * 9 := by nlinarith
      _ ≤ 6000 * x ^ (5 / 2 - ε / 3) := by
          have : 0 ≤ x ^ (5 / 2 - ε / 3) := (Real.rpow_pos_of_pos hx0 _).le
          nlinarith
  have E5 : ∀ᶠ x : ℝ in atTop, (100 : ℝ) ≤ x := eventually_ge_atTop 100
  have Eall := (E1.and (E2.and (E3.and (E4.and E5))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually Eall)
  refine ⟨N₀, fun n hn m L d P hP δ hδ0 hδM hL hd hm => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hN₀ n hn
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast e5
  have hx0 : 0 < (n : ℝ) := by linarith
  have hk1 : (n : ℝ) ^ b ≤ kC ε n := Nat.le_ceil _
  have hk2 : (kC ε n : ℝ) < (n : ℝ) ^ b + 1 := Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hx0 b).le
  have hM1 : 2 * (n : ℝ) ^ a + 57 ≤ MC ε n := by
    unfold MC; push_cast; linarith [Nat.le_ceil (2 * (n : ℝ) ^ (ε / 100))]
  have hM2 : (MC ε n : ℝ) < 2 * (n : ℝ) ^ a + 58 := by
    unfold MC; push_cast
    linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (n : ℝ) ^ (ε / 100) by positivity)]
  have hM : 1 ≤ MC ε n := by unfold MC; omega
  generalize kC ε n = k at hk1 hk2 ⊢
  generalize MC ε n = M at hM1 hM2 hM hδM ⊢
  have hxa0 : 0 ≤ (n : ℝ) ^ a := (Real.rpow_pos_of_pos hx0 a).le
  -- hypotheses of nl_u_half
  have hx' : (L : ℝ) * (3 / 5) ^ M ≤ 1 / 2 ^ 40 := list_small hL (by linarith)
  have hk : 16 * M ^ 3 ≤ k := by
    have h7 : (n : ℝ) ^ (7 * a) * (n : ℝ) ^ (3 * a) = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hx0]; congr 1; rw [hb, ha]; ring
    have h3 : (2 * (n : ℝ) ^ a + 58) ^ 3 ≤ 216000 * (n : ℝ) ^ (3 * a) := by
      have h1 : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow (le_trans (by norm_num) hn100) ha0.le
      have : 2 * (n : ℝ) ^ a + 58 ≤ 60 * (n : ℝ) ^ a := by linarith
      calc (2 * (n : ℝ) ^ a + 58) ^ 3 ≤ (60 * (n : ℝ) ^ a) ^ 3 := by gcongr
        _ = 216000 * ((n : ℝ) ^ a) ^ 3 := by ring
        _ = 216000 * (n : ℝ) ^ (3 * a) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
    have : (16 * M ^ 3 : ℝ) ≤ k := by
      have hM3 : (M : ℝ) ^ 3 ≤ (2 * (n : ℝ) ^ a + 58) ^ 3 := by
        gcongr
      have hpos : 0 ≤ (n : ℝ) ^ (3 * a) := (Real.rpow_pos_of_pos hx0 _).le
      nlinarith
    exact_mod_cast this
  have hn400 : k + 400 ≤ n := by
    have : (k : ℝ) + 400 ≤ (n : ℝ) := by rw [Real.rpow_one] at e2; linarith
    exact_mod_cast this
  have hnk : (n : ℝ) ^ k * 2 ^ (2 * k + 45) ≤ 2 ^ n := by
    have hl : Real.log ((n : ℝ) ^ k * 2 ^ (2 * k + 45)) ≤ Real.log ((2 : ℝ) ^ n) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      have hlogx : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (le_trans (by norm_num) hn100)
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc (k : ℝ) * Real.log (n : ℝ) + (2 * k + 45) * Real.log 2
          ≤ ((n : ℝ) ^ b + 1) * Real.log (n : ℝ) + (2 * ((n : ℝ) ^ b + 1) + 45) * Real.log 2 := by gcongr
        _ ≤ (n : ℝ) * Real.log 2 := e3
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hl
  have hm1 : (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5) ≤ m := by
    have hlogx : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (le_trans (by norm_num) hn100)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hlM : Real.log M ≤ Real.log (2 * (n : ℝ) ^ a + 58) :=
      Real.log_le_log hM0 hM2.le
    have hkl : (k : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) ^ b + 1) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right hk2.le hlogx
    have hAB : (k : ℝ) * Real.log (n : ℝ) + Real.log M + 5
        ≤ ((n : ℝ) ^ b + 1) * Real.log (n : ℝ) + Real.log (2 * (n : ℝ) ^ a + 58) + 5 := by linarith
    have hs : 0 ≤ 27 * (4 * Real.sqrt (n : ℝ) + 5) := by positivity
    calc (4 * Real.sqrt n + 5) * 27 * (k * Real.log n + Real.log M + 5)
        = 27 * (4 * Real.sqrt (n : ℝ) + 5) * ((k : ℝ) * Real.log (n : ℝ) + Real.log M + 5) := by ring
      _ ≤ 27 * (4 * Real.sqrt (n : ℝ) + 5) * (((n : ℝ) ^ b + 1) * Real.log (n : ℝ) + Real.log (2 * (n : ℝ) ^ a + 58) + 5) :=
          mul_le_mul_of_nonneg_left hAB hs
      _ ≤ 6000 * (n : ℝ) ^ (5 / 2 - ε / 3) := e4
      _ ≤ m := hm
  have hm2 : (4 * Real.sqrt n + 5) * (10 / 3) * (100 * (d + 1) ^ 2) ≤ m := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hn100
    have hxe1 : 1 ≤ (n : ℝ) ^ (1 - ε / 6) := Real.one_le_rpow hn1 (by linarith)
    have hd1 : (d : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 - ε / 6) := by linarith
    have hd2 : ((d : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ (2 - ε / 3) := by
      have hsq2 : ((n : ℝ) ^ (1 - ε / 6)) ^ 2 = (n : ℝ) ^ (2 - ε / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
      have : (2 * (n : ℝ) ^ (1 - ε / 6)) ^ 2 = 4 * (n : ℝ) ^ (2 - ε / 3) := by
        rw [mul_pow, hsq2]; norm_num
      calc ((d : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) ^ (1 - ε / 6)) ^ 2 := by gcongr
        _ = 4 * (n : ℝ) ^ (2 - ε / 3) := this
    have hs10 : 10 ≤ Real.sqrt (n : ℝ) := by
      rw [show (10 : ℝ) = Real.sqrt 100 by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt e5
    have hs : 4 * Real.sqrt (n : ℝ) + 5 ≤ 9 / 2 * Real.sqrt (n : ℝ) := by linarith
    have hprod : Real.sqrt (n : ℝ) * (n : ℝ) ^ (2 - ε / 3) = (n : ℝ) ^ (5 / 2 - ε / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; ring_nf
    have hp : 0 ≤ (n : ℝ) ^ (2 - ε / 3) := (Real.rpow_pos_of_pos hx0 _).le
    have hdd : (10 / 3) * (100 * ((d : ℝ) + 1) ^ 2) ≤ (10 / 3) * (100 * (4 * (n : ℝ) ^ (2 - ε / 3))) := by
      linarith
    calc (4 * Real.sqrt n + 5) * (10 / 3) * (100 * ((d : ℝ) + 1) ^ 2)
        = (4 * Real.sqrt n + 5) * ((10 / 3) * (100 * ((d : ℝ) + 1) ^ 2)) := by ring
      _ ≤ (9 / 2 * Real.sqrt (n : ℝ)) * ((10 / 3) * (100 * (4 * (n : ℝ) ^ (2 - ε / 3)))) :=
          mul_le_mul hs hdd (by positivity) (by positivity)
      _ = 6000 * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (2 - ε / 3)) := by ring
      _ = 6000 * (n : ℝ) ^ (5 / 2 - ε / 3) := by rw [hprod]
      _ ≤ m := hm
  exact nl_u_half P hP hM hx' hk hn400 hnk hm1 hm2 hδ0 hδM

end NLU

end

end ProblemQ
