import ProblemQ.Level3

/-!
# Random threshold circuits restricted to a column

A gate is `γ = (w, t) ∈ (Fin n → Bool) × T`, computing `x ↦ 1[t ≤ ∑ⱼ sgn(w j) sgn(x j)]`.
A column is given by a live set `I` and an outside assignment `z`; its points are
`merge I z y` for `y : I → Bool`.
-/

open Finset BigOperators
open scoped RealInnerProductSpace

namespace ProblemQ

noncomputable section

variable {n : ℕ} (T : Finset ℤ)

/-- Gate space. -/
abbrev Gate (n : ℕ) (T : Finset ℤ) := (Fin n → Bool) × T

/-- Gate value. -/
def gv (γ : Gate n T) (x : Fin n → Bool) : ℝ :=
  if (((γ.2 : ℤ)) : ℝ) ≤ ∑ j, sgn (γ.1 j) * sgn (x j) then 1 else 0

/-- Point of a column. -/
def merge (I : Finset (Fin n)) (z : Fin n → Bool) (y : I → Bool) : Fin n → Bool :=
  fun j => if h : j ∈ I then y ⟨j, h⟩ else z j

/-- Outside part of the threshold. -/
def outside (I : Finset (Fin n)) (z : Fin n → Bool) (w : {j // j ∉ I} → Bool) : ℝ :=
  ∑ j : {j // j ∉ I}, sgn (w j) * sgn (z j)

/-- Effective threshold on the column. -/
def tau (I : Finset (Fin n)) (z : Fin n → Bool) (θ : ({j // j ∉ I} → Bool) × T) : ℝ :=
  (((θ.2 : ℤ)) : ℝ) - outside I z θ.1

/-- Splitting a gate into its live part and the rest. -/
def splitGate (I : Finset (Fin n)) :
    Gate n T ≃ (I → Bool) × (({j // j ∉ I} → Bool) × T) :=
  ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ I) (fun _ => Bool)).prodCongr
    (Equiv.refl T)).trans (Equiv.prodAssoc _ _ _)

lemma gv_merge (I : Finset (Fin n)) (z : Fin n → Bool) (γ : Gate n T) (y : I → Bool) :
    gv T γ (merge I z y)
      = gateFun ((splitGate T I γ).1) (tau T I z (splitGate T I γ).2) y := by
  obtain ⟨w, t⟩ := γ
  have hsplit : ∑ j, sgn (w j) * sgn (merge I z y j)
      = ∑ i : I, sgn (w i) * sgn (y i) + ∑ j : {j // j ∉ I}, sgn (w j) * sgn (z j) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ I)]
    have h1 : ∀ i : {j // j ∈ I}, merge I z y i = y i := fun i => by
      simp [merge, i.2]
    have h2 : ∀ i : {j // j ∉ I}, merge I z y i = z i := fun i => by
      simp [merge, i.2]
    simp only [h1, h2]
    congr 1
    exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  unfold gv gateFun tau outside
  simp only [splitGate, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.piEquivPiSubtypeProd_apply, Equiv.coe_refl, id, Equiv.prodAssoc_apply]
  rw [hsplit]
  congr 1
  apply propext
  constructor <;> intro H <;> linarith

/-- Level-3 vector of a gate on the column. -/
def colVec (I : Finset (Fin n)) (z : Fin n → Bool) (γ : Gate n T) :
    EuclideanSpace ℝ (L3 I) :=
  lvl3 (fun y => gv T γ (merge I z y))

lemma colVec_eq (I : Finset (Fin n)) (z : Fin n → Bool) (γ : Gate n T) :
    colVec T I z γ = gateVec (tau T I z) (splitGate T I γ) := by
  unfold colVec gateVec
  congr 1
  funext y
  exact gv_merge T I z γ y

/-- Fraction of outside data hitting the atom `τ = 1`. -/
def pAtom (I : Finset (Fin n)) (z : Fin n → Bool) [Nonempty T] : ℝ :=
  ((univ.filter (fun θ : ({j // j ∉ I} → Bool) × T => tau T I z θ = 1)).card : ℝ)
    / Fintype.card (({j // j ∉ I} → Bool) × T)

/-- Covariance lower bound for the column vectors of a random gate. -/
theorem colVec_var [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool) {f : ℝ} (hf0 : 0 ≤ f)
    (hf : ∀ S : L3 I, f ≤ fourier (thrFun 1) S.1 ^ 2) (v : EuclideanSpace ℝ (L3 I)) :
    2 * (pAtom T I z * f) * ‖v‖ ^ 2 ≤
      (∑ γ, ∑ γ', ⟪v, colVec T I z γ - colVec T I z γ'⟫ ^ 2)
        / (Fintype.card (Gate n T) : ℝ) ^ 2 := by
  have h := gateVec_var (Θ := ({j // j ∉ I} → Bool) × T) (tau T I z) hf0 hf v
  have hcard : Fintype.card (Gate n T)
      = Fintype.card ((I → Bool) × (({j // j ∉ I} → Bool) × T)) :=
    Fintype.card_congr (splitGate T I)
  simp_rw [colVec_eq]
  rw [hcard]
  rw [Equiv.sum_comp (splitGate T I) (fun γ => ∑ γ', ⟪v, gateVec (tau T I z) γ
    - gateVec (tau T I z) (splitGate T I γ')⟫ ^ 2)]
  rw [Fintype.sum_congr _ _ (fun p => Equiv.sum_comp (splitGate T I)
    (fun p' => ⟪v, gateVec (tau T I z) p - gateVec (tau T I z) p'⟫ ^ 2))]
  exact h

variable {m : ℕ}

/-- The linear form computed on a column. -/
def gsum (ω : Fin m → Gate n T) (α : Fin m → ℝ) (I : Finset (Fin n)) (z : Fin n → Bool)
    (y : I → Bool) : ℝ :=
  ∑ i, α i * gv T (ω i) (merge I z y)

/-- Window certification of a column: at most `δ 2^|I|` points deviate by more than `W`. -/
def certified (ω : Fin m → Gate n T) (α : Fin m → ℝ) (I : Finset (Fin n)) (z : Fin n → Bool)
    (c : (I → Bool) → ℝ) (W δ : ℝ) : Prop :=
  ((univ.filter (fun y : I → Bool => W < |gsum T ω α I z y - c y|)).card : ℝ)
    ≤ δ * 2 ^ Fintype.card I

instance (ω : Fin m → Gate n T) (α : Fin m → ℝ) (I : Finset (Fin n)) (z : Fin n → Bool)
    (c : (I → Bool) → ℝ) (W δ : ℝ) : Decidable (certified T ω α I z c W δ) := by
  unfold certified; infer_instance

lemma gv_nonneg (γ : Gate n T) (x : Fin n → Bool) : 0 ≤ gv T γ x := by
  unfold gv; split_ifs <;> norm_num

lemma gv_le_one (γ : Gate n T) (x : Fin n → Bool) : gv T γ x ≤ 1 := by
  unfold gv; split_ifs <;> norm_num

lemma abs_gsum_le (ω : Fin m → Gate n T) (α : Fin m → ℝ)
    (hα : ∀ i, α i = 1 ∨ α i = -1 ∨ α i = 0) (I : Finset (Fin n)) (z : Fin n → Bool)
    (y : I → Bool) : |gsum T ω α I z y| ≤ m := by
  unfold gsum
  calc |∑ i, α i * gv T (ω i) (merge I z y)| ≤ ∑ i, |α i * gv T (ω i) (merge I z y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
        refine sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        have h1 : |α i| ≤ 1 := by rcases hα i with h | h | h <;> simp [h]
        have h2 : |gv T (ω i) (merge I z y)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [gv_nonneg T (ω i) (merge I z y),
            gv_le_one T (ω i) (merge I z y)]
        nlinarith [abs_nonneg (α i), abs_nonneg (gv T (ω i) (merge I z y))]
    _ = m := by simp

/-- Clipping a center to `[-B, B]`. -/
def clip (B : ℝ) (c : ℝ) : ℝ := max (-B) (min B c)

lemma abs_sub_clip_le {B g c : ℝ} (hg : |g| ≤ B) : |g - clip B c| ≤ |g - c| := by
  unfold clip
  rw [abs_le] at hg
  by_cases h1 : c ≤ -B
  · have : max (-B) (min B c) = -B := by
      rw [min_eq_right (by linarith), max_eq_left h1]
    rw [this, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  by_cases h2 : B ≤ c
  · have : max (-B) (min B c) = B := by
      rw [min_eq_left h2, max_eq_right (by linarith)]
    rw [this, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have : max (-B) (min B c) = c := by
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    rw [this]

lemma abs_sub_clip_le_two {B g c : ℝ} (hg : |g| ≤ B) : |g - clip B c| ≤ 2 * B := by
  have hB : 0 ≤ B := (abs_nonneg g).trans hg
  have hc : |clip B c| ≤ B := by
    unfold clip; rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  calc |g - clip B c| ≤ |g| + |clip B c| := abs_sub _ _
    _ ≤ 2 * B := by linarith

lemma fourier_comb {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Fin m → (ι → Bool) → ℝ)
    (α : Fin m → ℝ) (c : (ι → Bool) → ℝ) (S : Finset ι) :
    fourier (fun y => ∑ i, α i * f i y - c y) S
      = ∑ i, α i * fourier (f i) S - fourier c S := by
  unfold fourier
  simp only [sub_mul, sum_sub_distrib, sum_mul, sub_div, sum_div]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl (fun i _ => ?_)
  rw [mul_sum]
  exact sum_congr rfl (fun y _ => by ring)

lemma lvl3_comb {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Fin m → (ι → Bool) → ℝ)
    (α : Fin m → ℝ) (c : (ι → Bool) → ℝ) :
    ∑ i, α i • lvl3 (f i) - lvl3 c = lvl3 (fun y => ∑ i, α i * f i y - c y) := by
  ext S
  rw [lvl3_apply, fourier_comb]
  simp [lvl3_apply, WithLp.ofLp_sum]

lemma lvl3_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → Bool) → ℝ) :
    lvl3 f - lvl3 g = lvl3 (fun y => f y - g y) := by
  ext S
  simp [lvl3_apply, fourier_sub]

lemma norm_lvl3_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (hf : ∀ y, |f y| ≤ 1) : ‖lvl3 f‖ ≤ 1 := by
  have h := norm_lvl3_sq_le f
  have hsum : ∑ x, f x ^ 2 ≤ (2 : ℝ) ^ Fintype.card ι := by
    calc ∑ x, f x ^ 2 ≤ ∑ _x : ι → Bool, (1 : ℝ) := by
          refine sum_le_sum (fun x _ => ?_)
          have := hf x
          rw [← sq_abs]; nlinarith [abs_nonneg (f x)]
      _ = (2 : ℝ) ^ Fintype.card ι := by
          simp [Fintype.card_fun, Fintype.card_bool]
  have h1 : ‖lvl3 f‖ ^ 2 ≤ 1 := by
    refine h.trans ?_
    rw [div_le_one (by positivity)]; exact hsum
  nlinarith [norm_nonneg (lvl3 f)]

lemma colVec_diam (I : Finset (Fin n)) (z : Fin n → Bool) (γ γ' : Gate n T) :
    ‖colVec T I z γ - colVec T I z γ'‖ ≤ 1 := by
  unfold colVec
  rw [lvl3_sub]
  apply norm_lvl3_le_one
  intro y
  rw [abs_le]
  constructor <;> linarith [gv_nonneg T γ (merge I z y), gv_le_one T γ (merge I z y),
    gv_nonneg T γ' (merge I z y), gv_le_one T γ' (merge I z y)]

/-- A certified column puts the level-3 vector in a small ball. -/
lemma certified_ball (ω : Fin m → Gate n T) (α : Fin m → ℝ)
    (hα : ∀ i, α i = 1 ∨ α i = -1 ∨ α i = 0) (I : Finset (Fin n)) (z : Fin n → Bool)
    (c : (I → Bool) → ℝ) {W δ : ℝ} (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hcert : certified T ω α I z c W δ) :
    ‖∑ i, α i • colVec T I z (ω i) - lvl3 (fun y => clip m (c y))‖
      ≤ Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) := by
  unfold colVec
  rw [lvl3_comb (fun i y => gv T (ω i) (merge I z y)) α (fun y => clip m (c y))]
  set g : (I → Bool) → ℝ := fun y => gsum T ω α I z y with hg
  have hgsum : ∀ y, (∑ i, α i * gv T (ω i) (merge I z y)) = g y := fun y => rfl
  simp_rw [hgsum]
  apply Real.le_sqrt_of_sq_le
  refine (norm_lvl3_sq_le _).trans ?_
  set D : ℝ := (2 : ℝ) ^ Fintype.card I with hD
  have hDpos : 0 < D := by positivity
  rw [div_le_iff₀ hDpos]
  set bad := univ.filter (fun y : I → Bool => W < |gsum T ω α I z y - c y|) with hbad
  have hpt : ∀ y, (g y - clip m (c y)) ^ 2
      ≤ W ^ 2 + (if y ∈ bad then 4 * (m : ℝ) ^ 2 else 0) := by
    intro y
    have hgm := abs_gsum_le T ω α hα I z y
    by_cases hy : y ∈ bad
    · rw [if_pos hy]
      have := abs_sub_clip_le_two (c := c y) hgm
      have h2 : (g y - clip m (c y)) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith [sq_nonneg W]
    · rw [if_neg hy, add_zero]
      simp only [hbad, mem_filter, mem_univ, true_and, not_lt] at hy
      have := abs_sub_clip_le (c := c y) hgm
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (this.trans hy) 2
  calc ∑ y, (g y - clip m (c y)) ^ 2
      ≤ ∑ y : I → Bool, (W ^ 2 + (if y ∈ bad then 4 * (m : ℝ) ^ 2 else 0)) := sum_le_sum (fun y _ => hpt y)
    _ = D * W ^ 2 + (bad.card : ℝ) * (4 * (m : ℝ) ^ 2) := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_mem, univ_inter,
          sum_const, nsmul_eq_mul]
        simp [hD, Fintype.card_fun, Fintype.card_bool]
    _ ≤ D * W ^ 2 + δ * D * (4 * (m : ℝ) ^ 2) := by
        gcongr
        exact hcert
    _ = (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) * D := by ring

lemma card_L3 (I : Finset (Fin n)) :
    Fintype.card (L3 I) = (Fintype.card I).choose 3 := by
  unfold L3
  exact Fintype.card_finset_len 3

/-- **Per-column bound.** For a fixed column, coefficient vector and center rule, the fraction
of random circuits that certify the column is exponentially small in `C(|I|, 3)`. -/
theorem column_bound [Nonempty T] (I : Finset (Fin n)) (h : ℕ) (hh : 1 ≤ h)
    (hI : I.card = 2 * h + 3) (z : Fin n → Bool) (α : Fin m → ℝ)
    (hα : ∀ i, α i = 1 ∨ α i = -1 ∨ α i = 0) (c : (I → Bool) → ℝ) {W δ : ℝ}
    (hW : 0 < W) (hδ : 0 ≤ δ) :
    ((univ.filter (fun ω : Fin m → Gate n T => certified T ω α I z c W δ)).card : ℝ)
        / (Fintype.card (Gate n T) : ℝ) ^ m
      ≤ Real.exp ((Fintype.card (L3 I) : ℝ) / 2) *
        ((Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ^ 2 / (2 * (Fintype.card (L3 I) : ℝ)) /
            (Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ^ 2 / (2 * (Fintype.card (L3 I) : ℝ)) +
              (43 / 96) * (pAtom T I z * (1 / (64 * (h : ℝ) * (h + 1) ^ 2))) *
                ((univ.filter (fun i => α i ≠ 0)).card : ℝ))) ^ ((Fintype.card (L3 I) : ℝ) / 2)
          + 2 ^ ((Fintype.card (L3 I) : ℝ) / 2) *
            Real.exp (-(Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ^ 2
              / (2 * (Fintype.card (L3 I) : ℝ))) / (2 * 1 ^ 2))) := by
  have hcardI : Fintype.card I = 2 * h + 3 := by simp [hI]
  set f : ℝ := 1 / (64 * (h : ℝ) * (h + 1) ^ 2) with hfdef
  have hf0 : 0 ≤ f := by positivity
  have hf : ∀ S : L3 I, f ≤ fourier (thrFun 1) S.1 ^ 2 :=
    fun S => fourier_thr1_sq_ge h hh hcardI S.1 S.2
  have hvar := colVec_var T I z hf0 hf
  have hp : 0 ≤ pAtom T I z := by unfold pAtom; positivity
  have hN : 0 < Fintype.card (L3 I) := by
    rw [card_L3, hcardI]; exact Nat.choose_pos (by omega)
  have hR : 0 < Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsub : univ.filter (fun ω : Fin m → Gate n T => certified T ω α I z c W δ)
      ⊆ univ.filter (fun ω : Fin m → Gate n T =>
          ‖(∑ i, α i • colVec T I z (ω i)) - lvl3 (fun y => clip m (c y))‖
            ≤ Real.sqrt (W ^ 2 + 4 * δ * (m : ℝ) ^ 2)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact certified_ball T ω α hα I z c hW.le hδ hω
  have hcard := (Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)
  have hpos : (0 : ℝ) < (Fintype.card (Gate n T) : ℝ) ^ m := by
    have : 0 < Fintype.card (Gate n T) := Fintype.card_pos
    positivity
  refine (div_le_div_of_nonneg_right hcard hpos.le).trans ?_
  exact small_ball hN (colVec T I z) α hα (mul_nonneg hp hf0) one_pos hR hvar
    (colVec_diam T I z) (lvl3 (fun y => clip m (c y)))

end

end ProblemQ
