import ProblemQ.Layering

/-!
# Theorem R3, uniform over live sets and columns

Theorem R3 (`layering_barrier`) fixes the live set `I` and bounds the *fraction* of dangerous
columns via Chebyshev and Markov. Here the per-column failure probability is made exponentially
small with Chernoff–Bernstein tails for the entries `Z_{SS'} = ∑ᵢ X_{iS} X_{iS'}`, so a union
bound over every live set `I` of size `k` and every column `z` goes through: for at least half of
all random circuits, **no** restriction `(I, z)` is dangerous.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

section Chernoff

variable {Γ : Type*} [Fintype Γ] {m : ℕ}

/-- Exponential moment of an i.i.d. sum factorizes. -/
lemma sum_exp_iid (g : Γ → ℝ) (lam : ℝ) :
    ∑ ω : Fin m → Γ, Real.exp (lam * ∑ i, g (ω i)) = (∑ γ, Real.exp (lam * g γ)) ^ m := by
  have hP := Fintype.prod_sum (fun (_ : Fin m) (γ : Γ) => Real.exp (lam * g γ))
  rw [prod_const, card_univ, Fintype.card_fin] at hP
  rw [hP]
  refine sum_congr rfl (fun ω _ => ?_)
  rw [mul_sum, Real.exp_sum]

/-- One-gate exponential moment: `E exp(λg) ≤ exp(λa + λ²b)` for `|g| ≤ 1`, `0 ≤ λ ≤ 1`. -/
lemma sum_exp_le (g : Γ → ℝ) (hg : ∀ γ, |g γ| ≤ 1) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {a b : ℝ} (ha : ∑ γ, g γ ≤ Fintype.card Γ * a) (hb : ∑ γ, g γ ^ 2 ≤ Fintype.card Γ * b) :
    ∑ γ, Real.exp (lam * g γ) ≤ Fintype.card Γ * Real.exp (lam * a + lam ^ 2 * b) := by
  have hpt : ∀ γ, Real.exp (lam * g γ) ≤ 1 + lam * g γ + lam ^ 2 * g γ ^ 2 := by
    intro γ
    have hx : |lam * g γ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg h0]
      calc lam * |g γ| ≤ 1 * 1 := mul_le_mul h1 (hg γ) (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
    have e : (lam * g γ) ^ 2 = lam ^ 2 * g γ ^ 2 := by ring
    linarith
  have hC : (0 : ℝ) ≤ Fintype.card Γ := Nat.cast_nonneg _
  calc ∑ γ, Real.exp (lam * g γ) ≤ ∑ γ, (1 + lam * g γ + lam ^ 2 * g γ ^ 2) :=
        sum_le_sum (fun γ _ => hpt γ)
    _ = Fintype.card Γ + lam * ∑ γ, g γ + lam ^ 2 * ∑ γ, g γ ^ 2 := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]; simp
    _ ≤ Fintype.card Γ + lam * (Fintype.card Γ * a) + lam ^ 2 * (Fintype.card Γ * b) := by
        gcongr
    _ = Fintype.card Γ * (1 + (lam * a + lam ^ 2 * b)) := by ring
    _ ≤ Fintype.card Γ * Real.exp (lam * a + lam ^ 2 * b) := by
        gcongr; linarith [Real.add_one_le_exp (lam * a + lam ^ 2 * b)]

/-- Upper tail of an i.i.d. sum (Chernoff–Bernstein). -/
def tail (g : Γ → ℝ) (t : ℝ) : Finset (Fin m → Γ) := univ.filter (fun ω => t ≤ ∑ i, g (ω i))

lemma card_tail_le (g : Γ → ℝ) (hg : ∀ γ, |g γ| ≤ 1) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {a b : ℝ} (ha : ∑ γ, g γ ≤ Fintype.card Γ * a) (hb : ∑ γ, g γ ^ 2 ≤ Fintype.card Γ * b)
    (t : ℝ) :
    ((tail (m := m) g t).card : ℝ)
      ≤ (Fintype.card Γ : ℝ) ^ m * Real.exp (m * (lam * a + lam ^ 2 * b) - lam * t) := by
  unfold tail
  calc ((univ.filter (fun ω : Fin m → Γ => t ≤ ∑ i, g (ω i))).card : ℝ)
      = ∑ ω ∈ univ.filter (fun ω : Fin m → Γ => t ≤ ∑ i, g (ω i)), (1 : ℝ) := by simp
    _ ≤ ∑ ω ∈ univ.filter (fun ω : Fin m → Γ => t ≤ ∑ i, g (ω i)),
          Real.exp (lam * ∑ i, g (ω i) - lam * t) := by
        refine sum_le_sum (fun ω hω => ?_)
        simp only [mem_filter, mem_univ, true_and] at hω
        exact Real.one_le_exp (by nlinarith)
    _ ≤ ∑ ω : Fin m → Γ, Real.exp (lam * ∑ i, g (ω i) - lam * t) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (Real.exp_pos _).le)
    _ = Real.exp (-(lam * t)) * ∑ ω : Fin m → Γ, Real.exp (lam * ∑ i, g (ω i)) := by
        rw [mul_sum]; refine sum_congr rfl (fun ω _ => ?_)
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (-(lam * t)) * (∑ γ, Real.exp (lam * g γ)) ^ m := by rw [sum_exp_iid]
    _ ≤ Real.exp (-(lam * t)) * (Fintype.card Γ * Real.exp (lam * a + lam ^ 2 * b)) ^ m := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (sum_nonneg (fun _ _ => (Real.exp_pos _).le)) (sum_exp_le g hg h0 h1 ha hb) m)
          (Real.exp_pos _).le
    _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul,
          show (m : ℝ) * (lam * a + lam ^ 2 * b) - lam * t
            = m * (lam * a + lam ^ 2 * b) + -(lam * t) by ring, Real.exp_add]
        ring

end Chernoff

section Entries

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool)

local notation "X" => colVec T I z

lemma coord_sq_le_one (γ : Gate n T) (S : L3 I) : X γ S ^ 2 ≤ 1 := by
  have h1 := norm_colVec_sq_le_one T I z γ
  rw [EuclideanSpace.norm_sq_eq] at h1
  have h2 := single_le_sum (f := fun S' => ‖X γ S'‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ S)
  simp only [Real.norm_eq_abs, sq_abs] at h1 h2
  linarith

lemma abs_coord_mul_le (γ : Gate n T) (S S' : L3 I) : |X γ S * X γ S'| ≤ 1 := by
  rw [abs_mul]
  have h1 := (sq_le_one_iff_abs_le_one _).mp (coord_sq_le_one T I z γ S)
  have h2 := (sq_le_one_iff_abs_le_one _).mp (coord_sq_le_one T I z γ S')
  exact mul_le_one₀ h1 (abs_nonneg _) h2

lemma Qm_nonneg : 0 ≤ Qm T I z := by unfold Qm; positivity

/-- Every level-3 coordinate carries `E X_S² = Q / N`. -/
lemma sum_coord_sq (hN : 0 < Fintype.card (L3 I)) (S : L3 I) :
    ∑ γ : Gate n T, X γ S ^ 2
      = Fintype.card (Gate n T) * (Qm T I z / Fintype.card (L3 I)) := by
  have hdiag : ∀ S' : L3 I, ∑ γ : Gate n T, X γ S' ^ 2 = ∑ γ : Gate n T, X γ S ^ 2 := by
    intro S'
    have h1 := gate_cross T I z S' S'
    have h2 := gate_cross T I z S S
    rw [if_pos rfl] at h1 h2
    simp_rw [sq]; rw [h1, h2, gate_diag_eq T I z S' S]
  have hsum : ∑ γ : Gate n T, ‖X γ‖ ^ 2
      = Fintype.card (L3 I) * ∑ γ : Gate n T, X γ S ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [sum_comm, sum_congr rfl (fun S' _ => hdiag S'), sum_const, card_univ, nsmul_eq_mul]
  have hC := card_gate_pos T (n := n)
  have hN' : (0 : ℝ) < Fintype.card (L3 I) := by exact_mod_cast hN
  unfold Qm; rw [hsum]; field_simp

/-- Entries `Z_{SS'} = ∑ᵢ X_{iS} X_{iS'}` of the empirical Gram matrix. -/
def Zc (ω : Fin m → Gate n T) (S S' : L3 I) : ℝ := ∑ i, X (ω i) S * X (ω i) S'

/-- All entries are at their typical size. -/
def tight (ω : Fin m → Gate n T) : Prop :=
  (∀ S S' : L3 I, S ≠ S' → |Zc T I z ω S S'|
      ≤ 2 * m * (Qm T I z / Fintype.card (L3 I)) / Real.sqrt (Fintype.card (L3 I))) ∧
    ∀ S : L3 I, m * (Qm T I z / Fintype.card (L3 I)) / 2 ≤ Zc T I z ω S S ∧
      Zc T I z ω S S ≤ 2 * m * (Qm T I z / Fintype.card (L3 I))

/-- Tight columns are good columns. -/
lemma tight_good (hN : 0 < Fintype.card (L3 I)) (ω : Fin m → Gate n T)
    (ht : tight T I z ω) : goodCol T I ω z := by
  obtain ⟨hoff, hdia⟩ := ht
  set N : ℝ := (Fintype.card (L3 I) : ℝ) with hNdef
  set Q := Qm T I z
  have hN0 : 0 < N := by rw [hNdef]; exact_mod_cast hN
  have hQ0 : 0 ≤ Q := Qm_nonneg T I z
  set q := Q / N with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set A : ℝ := (2 * m * q) ^ 2
  have hA0 : 0 ≤ A := sq_nonneg _
  have hterm : ∀ S S' : L3 I, Zc T I z ω S S' ^ 2 ≤ (if S = S' then A else 0) + A / N := by
    intro S S'
    have hB0 : 0 ≤ A / N := by positivity
    by_cases h : S = S'
    · subst h
      rw [if_pos rfl]
      obtain ⟨h1, h2⟩ := hdia S
      have h3 : 0 ≤ Zc T I z ω S S := le_trans (by positivity) h1
      have : Zc T I z ω S S ^ 2 ≤ A := pow_le_pow_left₀ h3 h2 2
      linarith
    · rw [if_neg h, zero_add]
      have h1 := hoff S S' h
      have h2 : Zc T I z ω S S' ^ 2 ≤ (2 * m * q / Real.sqrt N) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [div_pow, Real.sq_sqrt hN0.le] at h2
  refine ⟨?_, ?_⟩
  · show Ux T I z ω ≤ 16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N)
    have hU : Ux T I z ω ≤ N * (A + N * (A / N)) := by
      unfold Ux
      calc ∑ S : L3 I, ∑ S' : L3 I, (∑ i, X (ω i) S * X (ω i) S') ^ 2
          ≤ ∑ S : L3 I, ∑ S' : L3 I, ((if S = S' then A else 0) + A / N) :=
            sum_le_sum (fun S _ => sum_le_sum (fun S' _ => hterm S S'))
        _ = ∑ _S : L3 I, (A + N * (A / N)) := by
            refine sum_congr rfl (fun S _ => ?_)
            rw [sum_add_distrib, sum_ite_eq, if_pos (mem_univ S), sum_const, card_univ,
              nsmul_eq_mul]
        _ = N * (A + N * (A / N)) := by rw [sum_const, card_univ, nsmul_eq_mul]
    have hval : N * (A + N * (A / N)) = 8 * ((m : ℝ) ^ 2 * Q ^ 2 / N) := by
      simp only [A]; rw [hqdef]; field_simp; ring
    rw [hval] at hU
    have : 0 ≤ (m : ℝ) * Q := by positivity
    have : 0 ≤ (m : ℝ) ^ 2 * Q ^ 2 / N := by positivity
    linarith
  · show m * Q / 2 ≤ S2c T I z ω
    have hS : S2c T I z ω = ∑ S : L3 I, Zc T I z ω S S := by
      unfold S2c Zc
      simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, sq]
      exact sum_comm
    rw [hS]
    calc m * Q / 2 = ∑ _S : L3 I, m * q / 2 := by
          rw [sum_const, card_univ, nsmul_eq_mul, hqdef]; field_simp; rfl
      _ ≤ ∑ S : L3 I, Zc T I z ω S S := sum_le_sum (fun S _ => (hdia S).1)

open Classical in
/-- Exponentially few circuits make a given column non-tight. -/
lemma card_not_tight (hN : 16 ≤ Fintype.card (L3 I)) :
    ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ)
      ≤ (Fintype.card (Gate n T) : ℝ) ^ m * (4 * (Fintype.card (L3 I) : ℝ) ^ 2
          * Real.exp (-(m * Qm T I z / (Fintype.card (L3 I) : ℝ) ^ 2))) := by
  classical
  set N : ℝ := (Fintype.card (L3 I) : ℝ) with hNdef
  set Q := Qm T I z
  have hNpos : 0 < Fintype.card (L3 I) := by omega
  have hN0 : 0 < N := by rw [hNdef]; exact_mod_cast hNpos
  have hN16 : (16 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hQ0 : 0 ≤ Q := Qm_nonneg T I z
  set q := Q / N with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set G : ℝ := (Fintype.card (Gate n T) : ℝ) ^ m
  have hG0 : 0 ≤ G := by positivity
  set E : ℝ := Real.exp (-(m * Q / N ^ 2)) with hEdef
  have hE : E = Real.exp (-(m * q / N)) := by rw [hEdef, hqdef]; congr 1; field_simp
  set t : ℝ := 2 * m * q / Real.sqrt N
  set g : L3 I → L3 I → Gate n T → ℝ := fun S S' γ => X γ S * X γ S'
  have hg1 : ∀ S S' γ, |g S S' γ| ≤ 1 := fun S S' γ => abs_coord_mul_le T I z γ S S'
  have hgn1 : ∀ S S' γ, |(fun γ => -g S S' γ) γ| ≤ 1 := fun S S' γ => by
    simp only [abs_neg]; exact hg1 S S' γ
  have hC : (0 : ℝ) ≤ Fintype.card (Gate n T) := Nat.cast_nonneg _
  have hsq : ∀ S, ∑ γ : Gate n T, X γ S ^ 2 = Fintype.card (Gate n T) * q :=
    fun S => sum_coord_sq T I z hNpos S
  -- second moments
  have hb : ∀ S S', ∑ γ, g S S' γ ^ 2 ≤ Fintype.card (Gate n T) * q := by
    intro S S'
    rw [← hsq S]
    refine sum_le_sum (fun γ _ => ?_)
    have h1 := coord_sq_le_one T I z γ S'
    have h0 := sq_nonneg (X γ S)
    simp only [g, mul_pow]; nlinarith
  have hbn : ∀ S S', ∑ γ, (fun γ => -g S S' γ) γ ^ 2 ≤ Fintype.card (Gate n T) * q := by
    intro S S'; simp only [neg_sq]; exact hb S S'
  -- the four Chernoff bounds
  have hlam0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hlam1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr hN0)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
  have hl2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  have hlt : 1 / Real.sqrt N * t = 2 * m * q / N := by
    have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have hs0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
    simp only [t]
    rw [div_mul_div_comm, one_mul, hs]
  have hoff : ∀ S S', S ≠ S' → ((tail (m := m) (g S S') t).card : ℝ) ≤ G * E := by
    intro S S' hSS
    have ha : ∑ γ, g S S' γ ≤ Fintype.card (Gate n T) * 0 := by
      have := gate_cross T I z S S'
      rw [if_neg hSS] at this
      simp only [g, this, mul_zero, le_refl]
    have := card_tail_le (m := m) (g S S') (hg1 S S') hlam0 hlam1 ha (hb S S') t
    rw [hE]
    convert this using 2
    rw [hl2, hlt]; congr 1; ring
  have hoffn : ∀ S S', S ≠ S' →
      ((tail (m := m) (fun γ => -g S S' γ) t).card : ℝ) ≤ G * E := by
    intro S S' hSS
    have ha : ∑ γ, (fun γ => -g S S' γ) γ ≤ Fintype.card (Gate n T) * 0 := by
      have := gate_cross T I z S S'
      rw [if_neg hSS] at this
      simp only [g, sum_neg_distrib, this, neg_zero, mul_zero, le_refl]
    have := card_tail_le (m := m) (fun γ => -g S S' γ) (hgn1 S S') hlam0 hlam1 ha (hbn S S') t
    rw [hE]
    convert this using 2
    rw [hl2, hlt]; congr 1; ring
  have hEq4 : Real.exp (-(m * q / 4)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : m * q / N ≤ m * q / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
      (by linarith)
    linarith
  have hEq16 : Real.exp (-(m * q / 16)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : m * q / N ≤ m * q / 16 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
      hN16
    linarith
  have hdiag : ∀ S, ((tail (m := m) (g S S) (2 * m * q)).card : ℝ) ≤ G * E := by
    intro S
    have ha : ∑ γ, g S S γ ≤ Fintype.card (Gate n T) * q := by
      simp only [g, ← sq]; rw [hsq S]
    have := card_tail_le (m := m) (g S S) (hg1 S S) (lam := 1 / 2) (by norm_num) (by norm_num)
      ha (hb S S) (2 * m * q)
    calc _ ≤ G * Real.exp (m * (1 / 2 * q + (1 / 2) ^ 2 * q) - 1 / 2 * (2 * m * q)) := this
      _ = G * Real.exp (-(m * q / 4)) := by congr 2; ring
      _ ≤ G * E := by gcongr
  have hdiagn : ∀ S,
      ((tail (m := m) (fun γ => -g S S γ) (-(m * q / 2))).card : ℝ) ≤ G * E := by
    intro S
    have ha : ∑ γ, (fun γ => -g S S γ) γ ≤ Fintype.card (Gate n T) * (-q) := by
      simp only [g, sum_neg_distrib, ← sq]; rw [hsq S]; linarith
    have := card_tail_le (m := m) (fun γ => -g S S γ) (hgn1 S S) (lam := 1 / 4) (by norm_num)
      (by norm_num) ha (hbn S S) (-(m * q / 2))
    calc _ ≤ G * Real.exp (m * (1 / 4 * -q + (1 / 4) ^ 2 * q) - 1 / 4 * -(m * q / 2)) := this
      _ = G * Real.exp (-(m * q / 16)) := by congr 2; ring
      _ ≤ G * E := by gcongr
  -- union bound
  set offU := (univ.filter (fun p : L3 I × L3 I => p.1 ≠ p.2)).biUnion
    (fun p => tail (m := m) (g p.1 p.2) t ∪ tail (m := m) (fun γ => -g p.1 p.2 γ) t)
  set diaU := (univ : Finset (L3 I)).biUnion
    (fun S => tail (m := m) (g S S) (2 * m * q) ∪ tail (m := m) (fun γ => -g S S γ) (-(m * q / 2)))
  have hsub : univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω) ⊆ offU ∪ diaU := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hc
    apply hω
    have hnot : ∀ (g' : Gate n T → ℝ) (t' : ℝ) (s : Finset (Fin m → Gate n T)),
        tail (m := m) g' t' ⊆ s → ω ∉ s → ∑ i, g' (ω i) < t' := by
      intro g' t' s hs hns
      by_contra h; push Not at h
      exact hns (hs (by simp [tail, h]))
    have hZ : ∀ S S', ∑ i, g S S' (ω i) = Zc T I z ω S S' := fun S S' => rfl
    have hZn : ∀ S S', ∑ i, (fun γ => -g S S' γ) (ω i) = -Zc T I z ω S S' := by
      intro S S'; simp only [sum_neg_distrib]; rfl
    refine ⟨fun S S' hSS => ?_, fun S => ?_⟩
    · have hsO : ∀ s, s ⊆ tail (m := m) (g S S') t ∪ tail (m := m) (fun γ => -g S S' γ) t →
          s ⊆ offU ∪ diaU := by
        intro s hs
        refine hs.trans (subset_union_left.trans' ?_)
        intro x hx
        exact mem_biUnion.mpr ⟨(S, S'), by simp [hSS], hx⟩
      have h1 := hnot _ _ _ (hsO _ subset_union_left) hc
      have h2 := hnot _ _ _ (hsO _ subset_union_right) hc
      rw [hZ] at h1; rw [hZn] at h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hsD : ∀ s, s ⊆ tail (m := m) (g S S) (2 * m * q)
          ∪ tail (m := m) (fun γ => -g S S γ) (-(m * q / 2)) → s ⊆ offU ∪ diaU := by
        intro s hs
        refine hs.trans (subset_union_right.trans' ?_)
        intro x hx
        exact mem_biUnion.mpr ⟨S, mem_univ S, hx⟩
      have h1 := hnot _ _ _ (hsD _ subset_union_left) hc
      have h2 := hnot _ _ _ (hsD _ subset_union_right) hc
      rw [hZ] at h1; rw [hZn] at h2
      exact ⟨by linarith, by linarith⟩
  have hcardOff : ((univ.filter (fun p : L3 I × L3 I => p.1 ≠ p.2)).card : ℝ) ≤ N ^ 2 := by
    have : (univ.filter (fun p : L3 I × L3 I => p.1 ≠ p.2)).card ≤ Fintype.card (L3 I) ^ 2 := by
      calc _ ≤ (univ : Finset (L3 I × L3 I)).card := card_le_card (filter_subset _ _)
        _ = Fintype.card (L3 I) ^ 2 := by rw [card_univ, Fintype.card_prod, sq]
    rw [hNdef]; exact_mod_cast this
  have hOff : (offU.card : ℝ) ≤ N ^ 2 * (2 * (G * E)) := by
    calc (offU.card : ℝ)
        ≤ ∑ p ∈ univ.filter (fun p : L3 I × L3 I => p.1 ≠ p.2),
            ((tail (m := m) (g p.1 p.2) t ∪ tail (m := m) (fun γ => -g p.1 p.2 γ) t).card : ℝ) := by
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ _p ∈ univ.filter (fun p : L3 I × L3 I => p.1 ≠ p.2), 2 * (G * E) := by
          refine sum_le_sum (fun p hp => ?_)
          simp only [mem_filter, mem_univ, true_and] at hp
          calc _ ≤ ((tail (m := m) (g p.1 p.2) t).card : ℝ)
                + ((tail (m := m) (fun γ => -g p.1 p.2 γ) t).card : ℝ) := by
                exact_mod_cast card_union_le _ _
            _ ≤ G * E + G * E := add_le_add (hoff _ _ hp) (hoffn _ _ hp)
            _ = 2 * (G * E) := by ring
      _ = _ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N ^ 2 * (2 * (G * E)) := by gcongr
  have hDia : (diaU.card : ℝ) ≤ N * (2 * (G * E)) := by
    calc (diaU.card : ℝ)
        ≤ ∑ S : L3 I, ((tail (m := m) (g S S) (2 * m * q)
            ∪ tail (m := m) (fun γ => -g S S γ) (-(m * q / 2))).card : ℝ) := by
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ _S : L3 I, 2 * (G * E) := by
          refine sum_le_sum (fun S _ => ?_)
          calc _ ≤ ((tail (m := m) (g S S) (2 * m * q)).card : ℝ)
                + ((tail (m := m) (fun γ => -g S S γ) (-(m * q / 2))).card : ℝ) := by
                exact_mod_cast card_union_le _ _
            _ ≤ G * E + G * E := add_le_add (hdiag S) (hdiagn S)
            _ = 2 * (G * E) := by ring
      _ = N * (2 * (G * E)) := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hGE : 0 ≤ G * E := by positivity
  calc ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ)
      ≤ ((offU ∪ diaU).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ (offU.card : ℝ) + diaU.card := by exact_mod_cast card_union_le _ _
    _ ≤ N ^ 2 * (2 * (G * E)) + N * (2 * (G * E)) := add_le_add hOff hDia
    _ ≤ G * (4 * N ^ 2 * E) := by nlinarith

end Entries

section Uniform

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (W δ : ℝ)

open Classical in
/-- **Theorem R3, uniform version.** If the per-column Chernoff bound beats the number of
restrictions `C(n,k) · 2ⁿ`, then for at least half of all random circuits **no** restriction
`(I, z)` with `|I| = k` is dangerous. -/
theorem layering_barrier_uniform (k : ℕ) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hN : 2048 < k.choose 3)
    (hQ : ∀ I : Finset (Fin n), I.card = k → ∀ z,
      4096 ≤ m * Qm T I z ∧ 8 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ≤ m * Qm T I z)
    (hE : ∀ I : Finset (Fin n), I.card = k → ∀ z,
      (n.choose k : ℝ) * 2 ^ n * (4 * (k.choose 3 : ℝ) ^ 2
        * Real.exp (-(m * Qm T I z / (k.choose 3 : ℝ) ^ 2))) ≤ 1 / 2) :
    ((univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, danger T I W δ ω z)).card : ℝ)
      / (Fintype.card (Gate n T) : ℝ) ^ m ≤ 1 / 2 := by
  set G : ℝ := (Fintype.card (Gate n T) : ℝ) ^ m with hGdef
  have hG : 0 < G := by have := card_gate_pos T (n := n); positivity
  set P := (univ : Finset (Fin n)).powersetCard k
  have hcardL : ∀ I : Finset (Fin n), I.card = k → Fintype.card (L3 I) = k.choose 3 := by
    intro I hI; rw [card_L3]; simp [hI]
  have hsub : univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, danger T I W δ ω z)
      ⊆ P.biUnion (fun I => (univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω))) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    obtain ⟨I, hI, z, hd⟩ := hω
    refine mem_biUnion.mpr ⟨I, by simp [P, mem_powersetCard, hI], mem_biUnion.mpr
      ⟨z, mem_univ z, ?_⟩⟩
    simp only [mem_filter, mem_univ, true_and]
    intro ht
    have hNI : (2048 : ℝ) < Fintype.card (L3 I) := by rw [hcardL I hI]; exact_mod_cast hN
    have hpos : 0 < Fintype.card (L3 I) := by rw [hcardL I hI]; omega
    exact good_not_danger T I W δ ω z hW hδ hNI (hQ I hI z) (tight_good T I z hpos ω ht) hd
  -- each restriction contributes at most `G / (2 C(n,k) 2ⁿ)`
  have hP : (P.card : ℝ) = n.choose k := by
    simp [P, card_powersetCard]
  have hterm : ∀ I ∈ P, ∀ z : Fin n → Bool,
      ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ)
        ≤ G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) := by
    intro I hIP z
    have hI : I.card = k := (mem_powersetCard.mp hIP).2
    have hkn : k ≤ n := by
      have := card_le_univ I; rw [Fintype.card_fin] at this; omega
    have hch : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    have h16 : 16 ≤ Fintype.card (L3 I) := by rw [hcardL I hI]; omega
    have hc := card_not_tight T I z (m := m) h16
    rw [hcardL I hI] at hc
    have hE' := hE I hI z
    calc _ ≤ G * (4 * (k.choose 3 : ℝ) ^ 2
          * Real.exp (-(m * Qm T I z / (k.choose 3 : ℝ) ^ 2))) := hc
      _ ≤ G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          linarith
  have hsum : ((univ.filter (fun ω : Fin m → Gate n T =>
        ∃ I : Finset (Fin n), I.card = k ∧ ∃ z, danger T I W δ ω z)).card : ℝ) ≤ G / 2 := by
    calc _ ≤ ((P.biUnion (fun I => (univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ I ∈ P, (((univ : Finset (Fin n → Bool)).biUnion
          (fun z => univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω))).card : ℝ) := by
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ I ∈ P, ∑ z : Fin n → Bool,
          ((univ.filter (fun ω : Fin m → Gate n T => ¬ tight T I z ω)).card : ℝ) := by
          refine sum_le_sum (fun I _ => ?_)
          rw [← Nat.cast_sum]; exact Nat.cast_le.mpr card_biUnion_le
      _ ≤ ∑ I ∈ P, ∑ _z : Fin n → Bool, G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)) :=
          sum_le_sum (fun I hI => sum_le_sum (fun z _ => hterm I hI z))
      _ = (P.card : ℝ) * (2 ^ n * (G * (1 / 2 / ((n.choose k : ℝ) * 2 ^ n)))) := by
          simp [sum_const, Fintype.card_bool, nsmul_eq_mul]
      _ ≤ G / 2 := by
          rw [hP]
          rcases Nat.eq_zero_or_pos (n.choose k) with h0 | h0
          · rw [h0]; simp; positivity
          · have : (0 : ℝ) < n.choose k := by exact_mod_cast h0
            field_simp
            rfl
  rw [div_le_iff₀ hG]
  linarith

end Uniform

section UniformConcrete

variable {n m : ℕ}

/-- In the barrier regime, `m · E‖X‖² ≥ 90 n²` on every column. -/
lemma mQ_ge (h : ℕ) (hh : 1 ≤ h) (I : Finset (Fin n)) (hI : I.card = 2 * h + 3)
    (z : Fin n → Bool) (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m) :
    (90 : ℝ) * (n : ℝ) ^ 2 ≤ m * Qm (Tset n) I z := by
  have hcardI : Fintype.card I = 2 * h + 3 := by simp [hI]
  have hNL : (Fintype.card (L3 I) : ℝ) = ((2 * h + 3).choose 3 : ℕ) := by
    rw [card_L3, hcardI]
  have hq : (0 : ℝ) < 4 * Nat.sqrt n + 5 := by positivity
  have hQ := Qm_ge I z h hh hI
  have hp := pAtom_ge (n := n) I z
  have hrad : (2 * (rad n : ℝ) + 1) = 4 * (Nat.sqrt n : ℝ) + 5 := by
    unfold rad; push_cast; ring
  rw [hrad] at hp
  have hpq : 3 / 4 ≤ pAtom (Tset n) I z * (4 * Nat.sqrt n + 5) := by rwa [div_le_iff₀ hq] at hp
  have hfN := f_mul_N h hh
  rw [← hNL] at hfN
  set f : ℝ := 1 / (64 * (h : ℝ) * (h + 1) ^ 2)
  set N : ℝ := (Fintype.card (L3 I) : ℝ)
  set p := pAtom (Tset n) I z
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have h1 : (m : ℝ) * (N * p * f) ≤ m * Qm (Tset n) I z :=
    mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg m)
  have h2 : (m : ℝ) * p / 48 ≤ (m : ℝ) * (N * p * f) := by
    have : p / 48 ≤ N * p * f := by nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have h3 : (90 : ℝ) * (n : ℝ) ^ 2 ≤ (m : ℝ) * p / 48 := by
    have : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 * p ≤ m * p :=
      mul_le_mul_of_nonneg_right hm hp0
    nlinarith [sq_nonneg (n : ℝ)]
  linarith

open Classical in
/-- **Theorem R3, uniform and instantiated.** With `k = 2h+3`, `N = C(k,3) > 2048`, `N² ≤ n`
and `m ≥ 5800 (4⌊√n⌋+5) n²`: for at least half of all random circuits, no live set `I` of size
`k` and no column `z` is dangerous. -/
theorem layering_barrier_uniform_concrete (h : ℕ) (hh : 1 ≤ h)
    (hN : 2048 < (2 * h + 3).choose 3) (hNn : ((2 * h + 3).choose 3) ^ 2 ≤ n)
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    {W δ : ℝ} (hW0 : 0 ≤ W) (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = 2 * h + 3 ∧ ∃ z, danger (Tset n) I W δ ω z)).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m ≤ 1 / 2 := by
  set N : ℝ := (((2 * h + 3).choose 3 : ℕ) : ℝ) with hNdef
  have hN0 : (2048 : ℝ) < N := by rw [hNdef]; exact_mod_cast hN
  have hNn' : N ^ 2 ≤ n := by rw [hNdef]; exact_mod_cast hNn
  have hn : (4000000 : ℝ) ≤ n := by nlinarith
  apply layering_barrier_uniform (Tset n) W δ (2 * h + 3) hW0 hδ0 hN
  · intro I hI z
    have key := mQ_ge h hh I hI z hm
    constructor
    · nlinarith
    · have : W ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hW0 hWn 2
      nlinarith
  · intro I hI z
    have key := mQ_ge h hh I hI z hm
    have hNsq : 0 < N ^ 2 := by positivity
    -- exponent ≥ 90 n
    have hexp : (90 : ℝ) * n ≤ m * Qm (Tset n) I z / N ^ 2 := by
      rw [le_div_iff₀ hNsq]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hE : Real.exp (-(m * Qm (Tset n) I z / N ^ 2)) ≤ Real.exp (-(90 * n)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hch : (n.choose (2 * h + 3) : ℝ) ≤ 2 ^ n := by
      exact_mod_cast Nat.choose_le_two_pow n (2 * h + 3)
    -- 8 n 4ⁿ ≤ e^{90 n}
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h4 : (2 : ℝ) ^ n * 2 ^ n ≤ Real.exp (2 * n) := by
      rw [← pow_add, show 2 * (n : ℝ) = ((n + n : ℕ) : ℝ) * 1 by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) h2e _
    have h8 : 8 * (n : ℝ) ≤ Real.exp (8 * n) := by linarith [Real.add_one_le_exp (8 * (n : ℝ))]
    have hprod : 8 * (n : ℝ) * (2 ^ n * 2 ^ n) ≤ Real.exp (90 * n) := by
      calc 8 * (n : ℝ) * (2 ^ n * 2 ^ n) ≤ Real.exp (8 * n) * Real.exp (2 * n) :=
            mul_le_mul h8 h4 (by positivity) (Real.exp_pos _).le
        _ = Real.exp (10 * n) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (90 * n) := Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : Real.exp (90 * (n : ℝ)) * Real.exp (-(90 * n)) = 1 := by
      rw [← Real.exp_add]; simp
    have hEpos : 0 ≤ Real.exp (-(90 * (n : ℝ))) := (Real.exp_pos _).le
    calc (n.choose (2 * h + 3) : ℝ) * 2 ^ n * (4 * N ^ 2 * Real.exp (-(m * Qm (Tset n) I z / N ^ 2)))
        ≤ 2 ^ n * 2 ^ n * (4 * n * Real.exp (-(90 * n))) := by
          gcongr
      _ = (8 * (n : ℝ) * (2 ^ n * 2 ^ n)) * Real.exp (-(90 * n)) / 2 := by ring
      _ ≤ Real.exp (90 * n) * Real.exp (-(90 * n)) / 2 := by gcongr
      _ = 1 / 2 := by rw [hsplit]
