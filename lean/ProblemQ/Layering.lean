import ProblemQ.Final

/-!
# Theorem R3: limited-independence layerings cannot balance columns

A family `{α_a}` of `±1` layerings that is 4-wise independent (possibly chosen after seeing the
circuit) certifies, with a `y`-constant center, at most a `512/N`-ish fraction of its members on
all but a quarter of the columns, for at least half of all random circuits.
-/

open Finset BigOperators
open scoped RealInnerProductSpace

namespace ProblemQ

noncomputable section

section Symmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fourier coefficients of a symmetric threshold function depend only on `|S|`. -/
lemma fourier_thrFun_card (τ : ℝ) {S T : Finset ι} (h : S.card = T.card) :
    fourier (thrFun τ) S = fourier (thrFun τ) T := by
  classical
  have hc : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ T} := by simp [h]
  set e : {x // x ∈ S} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hc
  set σ : Equiv.Perm ι := e.extendSubtype
  have hmem : ∀ x, σ x ∈ T ↔ x ∈ S := by
    intro x
    constructor
    · intro hx; by_contra hS; exact (e.extendSubtype_not_mem x hS) hx
    · intro hS; exact e.extendSubtype_mem x hS
  have hmap : S.map σ.toEmbedding = T := by
    ext i; simp only [mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact (hmem j).2 hj
    · intro hi; exact ⟨σ.symm i, (hmem _).1 (by simpa using hi), by simp⟩
  unfold fourier
  congr 1
  conv_rhs => rw [← Equiv.sum_comp (σ.arrowCongr (Equiv.refl Bool))]
  refine sum_congr rfl (fun x _ => ?_)
  have h1 : thrFun τ ((σ.arrowCongr (Equiv.refl Bool)) x) = thrFun τ x := by
    unfold thrFun
    congr 2
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
    exact Equiv.sum_comp σ.symm (fun j => sgn (x j))
  have h2 : chi T ((σ.arrowCongr (Equiv.refl Bool)) x) = chi S x := by
    unfold chi
    rw [← hmap, prod_map]
    refine prod_congr rfl (fun j _ => ?_)
    simp [Equiv.arrowCongr_apply]
  rw [h1, h2]

end Symmetry

section Product

variable {Γ : Type*} [Fintype Γ] {m : ℕ}

lemma prod_ite_one (i : Fin m) (A B : Fin m → ℝ) :
    ∏ l, (if l = i then A l else B l) = A i * ∏ l ∈ univ.erase i, B l := by
  rw [← mul_prod_erase univ _ (mem_univ i), if_pos rfl]
  congr 1
  exact prod_congr rfl (fun l hl => by rw [if_neg (ne_of_mem_erase hl)])

lemma sum_ite_fun (c : Prop) [Decidable c] (a b : Γ → ℝ) :
    ∑ γ, (if c then a γ else b γ) = if c then ∑ γ, a γ else ∑ γ, b γ := by
  split_ifs <;> rfl

/-- `∑_ω f(ω i) = |Γ|^(m-1) ∑ f`. -/
lemma sum_omega_one (i : Fin m) (f : Γ → ℝ) :
    ∑ ω : Fin m → Γ, f (ω i) = (Fintype.card Γ : ℝ) ^ (m - 1) * ∑ γ, f γ := by
  have hP := Fintype.prod_sum (fun (l : Fin m) (γ : Γ) => if l = i then f γ else 1)
  have hl : ∀ ω : Fin m → Γ, ∏ l, (if l = i then f (ω l) else 1) = f (ω i) := by
    intro ω
    rw [prod_ite_one i (fun l => f (ω l)) (fun _ => 1)]; simp
  calc ∑ ω : Fin m → Γ, f (ω i)
      = ∑ ω : Fin m → Γ, ∏ l, (if l = i then f (ω l) else 1) :=
        sum_congr rfl (fun ω _ => (hl ω).symm)
    _ = ∏ l, ∑ γ, (if l = i then f γ else 1) := hP.symm
    _ = ∏ l, (if l = i then ∑ γ, f γ else ∑ _γ : Γ, (1 : ℝ)) :=
        prod_congr rfl (fun l _ => sum_ite_fun _ _ _)
    _ = (∑ γ, f γ) * ∏ l ∈ univ.erase i, ∑ _γ : Γ, (1 : ℝ) :=
        prod_ite_one i (fun _ => ∑ γ, f γ) (fun _ => ∑ _γ : Γ, (1 : ℝ))
    _ = (Fintype.card Γ : ℝ) ^ (m - 1) * ∑ γ, f γ := by
        rw [prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
        simp [mul_comm]

/-- `∑_ω f(ω i) g(ω j) = |Γ|^(m-2) (∑ f)(∑ g)` for `i ≠ j`. -/
lemma sum_omega_two (i j : Fin m) (hij : i ≠ j) (f g : Γ → ℝ) :
    ∑ ω : Fin m → Γ, f (ω i) * g (ω j)
      = (Fintype.card Γ : ℝ) ^ (m - 2) * ((∑ γ, f γ) * ∑ γ, g γ) := by
  have hP := Fintype.prod_sum (fun (l : Fin m) (γ : Γ) =>
    if l = i then f γ else if l = j then g γ else 1)
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩
  have hcard : ((univ.erase i).erase j).card = m - 2 := by
    rw [card_erase_of_mem hj, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  have hinner : ∀ (B : Fin m → ℝ) (b : ℝ),
      ∏ l ∈ univ.erase i, (if l = j then B l else b) = B j * b ^ (m - 2) := by
    intro B b
    rw [← mul_prod_erase (univ.erase i) _ hj, if_pos rfl]
    rw [prod_congr rfl (fun l hl => if_neg (ne_of_mem_erase hl)), prod_const, hcard]
  have hl : ∀ ω : Fin m → Γ,
      ∏ l, (if l = i then f (ω l) else if l = j then g (ω l) else 1) = f (ω i) * g (ω j) := by
    intro ω
    rw [prod_ite_one i (fun l => f (ω l)) (fun l => if l = j then g (ω l) else 1)]
    rw [hinner (fun l => g (ω l)) 1, one_pow, mul_one]
  calc ∑ ω : Fin m → Γ, f (ω i) * g (ω j)
      = ∑ ω : Fin m → Γ, ∏ l, (if l = i then f (ω l) else if l = j then g (ω l) else 1) :=
        sum_congr rfl (fun ω _ => (hl ω).symm)
    _ = ∏ l, ∑ γ, (if l = i then f γ else if l = j then g γ else 1) := hP.symm
    _ = ∏ l, (if l = i then ∑ γ, f γ else if l = j then ∑ γ, g γ else ∑ _γ : Γ, (1 : ℝ)) := by
        refine prod_congr rfl (fun l _ => ?_)
        split_ifs <;> rfl
    _ = (∑ γ, f γ) * ((∑ γ, g γ) * (∑ _γ : Γ, (1 : ℝ)) ^ (m - 2)) := by
        rw [prod_ite_one i (fun _ => ∑ γ, f γ)
          (fun l => if l = j then ∑ γ, g γ else ∑ _γ : Γ, (1 : ℝ))]
        rw [hinner (fun _ => ∑ γ, g γ)]
    _ = (Fintype.card Γ : ℝ) ^ (m - 2) * ((∑ γ, f γ) * ∑ γ, g γ) := by
        simp; ring

/-- Second moment of an i.i.d. sum. -/
lemma sum_omega_sq (g : Γ → ℝ) :
    ∑ ω : Fin m → Γ, (∑ i, g (ω i)) ^ 2
      = (m : ℝ) * (Fintype.card Γ : ℝ) ^ (m - 1) * ∑ γ, g γ ^ 2
        + ((m : ℝ) * m - m) * (Fintype.card Γ : ℝ) ^ (m - 2) * (∑ γ, g γ) ^ 2 := by
  have hexp : ∀ ω : Fin m → Γ, (∑ i, g (ω i)) ^ 2
      = ∑ i, g (ω i) ^ 2 + ∑ i, ∑ j ∈ univ.erase i, g (ω i) * g (ω j) := by
    intro ω
    rw [sq, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← add_sum_erase univ _ (mem_univ i), sq]
  have h1 : ∀ i : Fin m, ∑ ω : Fin m → Γ, g (ω i) ^ 2
      = (Fintype.card Γ : ℝ) ^ (m - 1) * ∑ γ, g γ ^ 2 :=
    fun i => sum_omega_one i (fun γ => g γ ^ 2)
  have h2 : ∀ i : Fin m, ∑ ω : Fin m → Γ, ∑ j ∈ univ.erase i, g (ω i) * g (ω j)
      = ((m : ℝ) - 1) * ((Fintype.card Γ : ℝ) ^ (m - 2) * (∑ γ, g γ) ^ 2) := by
    intro i
    rw [sum_comm]
    rw [sum_congr rfl (fun j hj => sum_omega_two i j (Ne.symm (ne_of_mem_erase hj)) g g)]
    rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : 1 ≤ m := by have := i.2; omega
    rw [Nat.cast_sub hm, sq]; push_cast; ring
  calc ∑ ω : Fin m → Γ, (∑ i, g (ω i)) ^ 2
      = ∑ i, ∑ ω : Fin m → Γ, g (ω i) ^ 2
        + ∑ i, ∑ ω : Fin m → Γ, ∑ j ∈ univ.erase i, g (ω i) * g (ω j) := by
        simp_rw [hexp]; rw [sum_add_distrib, sum_comm]
        congr 1
        exact sum_comm
    _ = _ := by
        rw [sum_congr rfl (fun i _ => h1 i), sum_congr rfl (fun i _ => h2 i)]
        rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        ring

end Product

section Moments

variable {n : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool)

local notation "X" => colVec T I z

lemma colVec_apply (γ : Gate n T) (S : L3 I) :
    X γ S = chi S.1 (splitGate T I γ).1
      * fourier (thrFun (tau T I z (splitGate T I γ).2)) S.1 := by
  rw [colVec_eq]; unfold gateVec; rw [lvl3_apply, fourier_gateFun]

/-- Level-3 cross moments of a random gate are diagonal. -/
lemma gate_cross (S S' : L3 I) :
    ∑ γ : Gate n T, X γ S * X γ S'
      = if S = S' then (2 : ℝ) ^ Fintype.card I *
          ∑ θ : ({j // j ∉ I} → Bool) × T, fourier (thrFun (tau T I z θ)) S.1 ^ 2
        else 0 := by
  simp_rw [colVec_apply]
  rw [← Equiv.sum_comp (splitGate T I).symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, sum_comm]
  have : ∀ θ : ({j // j ∉ I} → Bool) × T,
      ∑ w : I → Bool, chi S.1 w * fourier (thrFun (tau T I z θ)) S.1
        * (chi S'.1 w * fourier (thrFun (tau T I z θ)) S'.1)
      = fourier (thrFun (tau T I z θ)) S.1 * fourier (thrFun (tau T I z θ)) S'.1
          * ∑ w : I → Bool, chi S.1 w * chi S'.1 w := by
    intro θ; rw [mul_sum]; exact sum_congr rfl (fun w _ => by ring)
  rw [sum_congr rfl (fun θ _ => this θ)]
  simp_rw [sum_chi_mul_chi]
  by_cases h : S = S'
  · subst h; simp [sq, mul_comm]; rw [mul_sum]
  · have h' : S.1 ≠ S'.1 := fun e => h (Subtype.ext e)
    simp [h, h']

/-- The diagonal moments are equal for all level-3 characters. -/
lemma gate_diag_eq (S S' : L3 I) :
    ∑ θ : ({j // j ∉ I} → Bool) × T, fourier (thrFun (tau T I z θ)) S.1 ^ 2
      = ∑ θ : ({j // j ∉ I} → Bool) × T, fourier (thrFun (tau T I z θ)) S'.1 ^ 2 := by
  refine sum_congr rfl (fun θ _ => ?_)
  rw [fourier_thrFun_card _ (S.2.trans S'.2.symm)]

lemma norm_colVec_sq_le_one (γ : Gate n T) : ‖X γ‖ ^ 2 ≤ 1 := by
  have := colVec_diam T I z γ γ
  have h0 : ‖X γ‖ ≤ 1 := by
    unfold colVec
    apply norm_lvl3_le_one
    intro y; rw [abs_le]
    constructor <;> linarith [gv_nonneg T γ (merge I z y), gv_le_one T γ (merge I z y)]
  nlinarith [norm_nonneg (X γ)]

/-- `Q = E ‖X‖²`. -/
def Qm : ℝ := (∑ γ : Gate n T, ‖X γ‖ ^ 2) / Fintype.card (Gate n T)

/-- Sum over `S, S'` of squared cross moments equals `Q² / N`. -/
lemma sum_cross_sq (hN : 0 < Fintype.card (L3 I)) :
    ∑ S : L3 I, ∑ S' : L3 I,
        ((∑ γ : Gate n T, X γ S * X γ S') / Fintype.card (Gate n T)) ^ 2
      = Qm T I z ^ 2 / Fintype.card (L3 I) := by
  set C : ℝ := (Fintype.card (Gate n T) : ℝ)
  have hC : 0 < C := by
    have : 0 < Fintype.card (Gate n T) := Fintype.card_pos
    rw [show C = (Fintype.card (Gate n T) : ℝ) from rfl]; exact_mod_cast this
  obtain ⟨S₀⟩ : Nonempty (L3 I) := Fintype.card_pos_iff.mp hN
  set d : ℝ := (2 : ℝ) ^ Fintype.card I *
    ∑ θ : ({j // j ∉ I} → Bool) × T, fourier (thrFun (tau T I z θ)) S₀.1 ^ 2
  have hdiag : ∀ S : L3 I, ∑ γ : Gate n T, X γ S * X γ S = d := by
    intro S; rw [gate_cross, if_pos rfl, gate_diag_eq T I z S S₀]
  have hQ : Qm T I z = (Fintype.card (L3 I) : ℝ) * d / C := by
    unfold Qm
    congr 1
    simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [sum_comm]
    simp_rw [← sq] at hdiag
    rw [sum_congr rfl (fun S _ => by simpa [sq] using hdiag S), sum_const, card_univ,
      nsmul_eq_mul]
  have hN' : (0 : ℝ) < Fintype.card (L3 I) := by exact_mod_cast hN
  calc ∑ S : L3 I, ∑ S' : L3 I, ((∑ γ : Gate n T, X γ S * X γ S') / C) ^ 2
      = ∑ _S : L3 I, (d / C) ^ 2 := by
        refine sum_congr rfl (fun S _ => ?_)
        rw [← add_sum_erase univ _ (mem_univ S)]
        rw [hdiag S]
        rw [sum_eq_zero (fun S' hS' => by
          rw [gate_cross, if_neg (Ne.symm (ne_of_mem_erase hS'))]; simp)]
        ring
    _ = Qm T I z ^ 2 / Fintype.card (L3 I) := by
        rw [sum_const, card_univ, nsmul_eq_mul, hQ]; field_simp

end Moments

section CircuitMoments

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool)

local notation "X" => colVec T I z

/-- `S₂ = ∑ᵢ ‖Xᵢ‖²`. -/
def S2c (ω : Fin m → Gate n T) : ℝ := ∑ i, ‖X (ω i)‖ ^ 2

/-- `U' = ∑_{S,S'} (∑ᵢ X_{iS} X_{iS'})²`, which dominates `∑_{i≠j} ⟪Xᵢ,Xⱼ⟫²`. -/
def Ux (ω : Fin m → Gate n T) : ℝ :=
  ∑ S : L3 I, ∑ S' : L3 I, (∑ i, X (ω i) S * X (ω i) S') ^ 2

lemma pow_split {C : ℝ} {m : ℕ} (hm : 2 ≤ m) :
    C ^ (m - 1) * C = C ^ m ∧ C ^ (m - 2) * C ^ 2 = C ^ m := by
  constructor
  · rw [← pow_succ]; congr 1; omega
  · rw [← pow_add]; congr 1; omega

lemma card_gate_pos : (0 : ℝ) < (Fintype.card (Gate n T) : ℝ) := by
  have : 0 < Fintype.card (Gate n T) := Fintype.card_pos
  exact_mod_cast this

lemma sum_normX_sq : ∑ γ : Gate n T, ‖X γ‖ ^ 2
    = (Fintype.card (Gate n T) : ℝ) * Qm T I z := by
  unfold Qm; have := card_gate_pos T (n := n); field_simp

lemma sum_S2c (hm : 2 ≤ m) :
    ∑ ω : Fin m → Gate n T, S2c T I z ω
      = (Fintype.card (Gate n T) : ℝ) ^ m * (m * Qm T I z) := by
  have p1 := (pow_split (C := (Fintype.card (Gate n T) : ℝ)) hm).1
  unfold S2c
  rw [sum_comm]
  rw [sum_congr rfl (fun i _ => sum_omega_one i (fun γ => ‖X γ‖ ^ 2))]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_normX_sq, ← p1]
  ring

lemma sum_S2c_var (hm : 2 ≤ m) :
    ∑ ω : Fin m → Gate n T, (S2c T I z ω - m * Qm T I z) ^ 2
      ≤ (Fintype.card (Gate n T) : ℝ) ^ m * (m * Qm T I z) := by
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (Fintype.card (Gate n T) : ℝ) := ⟨_, rfl⟩
  have hC : 0 < C := hCdef ▸ card_gate_pos T
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Qm T I z := ⟨_, rfl⟩
  have hsumX : ∑ γ : Gate n T, ‖X γ‖ ^ 2 = C * Q := by rw [hCdef, hQdef]; exact sum_normX_sq T I z
  have h4 : ∑ γ : Gate n T, (‖X γ‖ ^ 2) ^ 2 ≤ C * Q := by
    rw [← hsumX]
    refine sum_le_sum (fun γ _ => ?_)
    have h1 := norm_colVec_sq_le_one T I z γ
    nlinarith [sq_nonneg (‖X γ‖)]
  have hQ0 : 0 ≤ Q := by rw [hQdef]; unfold Qm; positivity
  have hsq := sum_omega_sq (m := m) (fun γ : Gate n T => ‖X γ‖ ^ 2)
  have hS := sum_S2c T I z hm
  rw [← hCdef, ← hQdef] at hS
  rw [← hCdef, hsumX] at hsq
  obtain ⟨p1, p2⟩ := pow_split (C := C) hm
  rw [← hCdef, ← hQdef]
  have hcard : ∑ _ω : Fin m → Gate n T, (1 : ℝ) = C ^ m := by
    simp [Fintype.card_fun, hCdef]
  have expand : ∑ ω : Fin m → Gate n T, (S2c T I z ω - m * Q) ^ 2
      = ∑ ω : Fin m → Gate n T, S2c T I z ω ^ 2 - 2 * (m * Q) * ∑ ω : Fin m → Gate n T, S2c T I z ω
        + C ^ m * (m * Q) ^ 2 := by
    have hpt : ∀ ω : Fin m → Gate n T, (S2c T I z ω - m * Q) ^ 2
        = S2c T I z ω ^ 2 - 2 * (m * Q) * S2c T I z ω + (m * Q) ^ 2 * 1 := fun ω => by ring
    rw [sum_congr rfl (fun ω _ => hpt ω), sum_add_distrib, sum_sub_distrib, ← mul_sum,
      ← mul_sum, hcard]
    ring
  have hS2sq : ∑ ω : Fin m → Gate n T, S2c T I z ω ^ 2
      = (m : ℝ) * C ^ (m - 1) * ∑ γ : Gate n T, (‖X γ‖ ^ 2) ^ 2
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (C * Q) ^ 2 := hsq
  rw [expand, hS, hS2sq]
  have hpow : 0 ≤ C ^ (m - 1) := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (m : ℝ) * C ^ (m - 1) * ∑ γ : Gate n T, (‖X γ‖ ^ 2) ^ 2
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (C * Q) ^ 2
        - 2 * (m * Q) * (C ^ m * (m * Q)) + C ^ m * (m * Q) ^ 2
      ≤ (m : ℝ) * C ^ (m - 1) * (C * Q)
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (C * Q) ^ 2
        - 2 * (m * Q) * (C ^ m * (m * Q)) + C ^ m * (m * Q) ^ 2 := by
        gcongr
    _ = C ^ m * (m * Q) - C ^ m * m * Q ^ 2 := by
        rw [show (m : ℝ) * C ^ (m - 1) * (C * Q) = m * (C ^ (m - 1) * C) * Q by ring, p1,
          show ((m : ℝ) * m - m) * C ^ (m - 2) * (C * Q) ^ 2
            = ((m : ℝ) * m - m) * (C ^ (m - 2) * C ^ 2) * Q ^ 2 by ring, p2]
        ring
    _ ≤ C ^ m * (m * Q) := by
        have : 0 ≤ C ^ m * m * Q ^ 2 := by positivity
        linarith

lemma sum_Ux (hm : 2 ≤ m) (hN : 0 < Fintype.card (L3 I)) :
    ∑ ω : Fin m → Gate n T, Ux T I z ω
      ≤ (Fintype.card (Gate n T) : ℝ) ^ m *
          (m * Qm T I z + (m : ℝ) ^ 2 * Qm T I z ^ 2 / Fintype.card (L3 I)) := by
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (Fintype.card (Gate n T) : ℝ) := ⟨_, rfl⟩
  have hC : 0 < C := hCdef ▸ card_gate_pos T
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Qm T I z := ⟨_, rfl⟩
  have hsumX : ∑ γ : Gate n T, ‖X γ‖ ^ 2 = C * Q := by rw [hCdef, hQdef]; exact sum_normX_sq T I z
  obtain ⟨p1, p2⟩ := pow_split (C := C) hm
  rw [← hCdef, ← hQdef]
  have hsq : ∀ S S' : L3 I, ∑ ω : Fin m → Gate n T, (∑ i, X (ω i) S * X (ω i) S') ^ 2
      = (m : ℝ) * C ^ (m - 1) * ∑ γ : Gate n T, (X γ S * X γ S') ^ 2
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (∑ γ : Gate n T, X γ S * X γ S') ^ 2 := by
    intro S S'; rw [hCdef]; exact sum_omega_sq (m := m) (fun γ => X γ S * X γ S')
  have hfirst : ∑ S : L3 I, ∑ S' : L3 I, ∑ γ : Gate n T, (X γ S * X γ S') ^ 2 ≤ C * Q := by
    rw [← hsumX, sum_congr rfl (fun S _ => sum_comm), sum_comm]
    refine sum_le_sum (fun γ _ => ?_)
    have h1 := norm_colVec_sq_le_one T I z γ
    have : ∑ S : L3 I, ∑ S' : L3 I, (X γ S * X γ S') ^ 2 = (‖X γ‖ ^ 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [sq (∑ S : L3 I, X γ S ^ 2), sum_mul_sum]
      exact sum_congr rfl (fun S _ => sum_congr rfl (fun S' _ => by ring))
    rw [this]; nlinarith [sq_nonneg (‖X γ‖)]
  have hsecond : ∑ S : L3 I, ∑ S' : L3 I, (∑ γ : Gate n T, X γ S * X γ S') ^ 2
      = C ^ 2 * (Q ^ 2 / Fintype.card (L3 I)) := by
    rw [hCdef, hQdef, ← sum_cross_sq T I z hN, mul_sum]; refine sum_congr rfl (fun S _ => ?_)
    rw [mul_sum]; refine sum_congr rfl (fun S' _ => ?_)
    have := card_gate_pos T (n := n)
    field_simp
  unfold Ux
  rw [sum_comm]
  rw [sum_congr rfl (fun S _ => sum_comm)]
  simp_rw [hsq]
  simp only [sum_add_distrib, ← mul_sum]
  rw [hsecond]
  have hpow : 0 ≤ C ^ (m - 1) := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmm : (0 : ℝ) ≤ (m : ℝ) * m - m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  calc (m : ℝ) * C ^ (m - 1) * (∑ S : L3 I, ∑ S' : L3 I, ∑ γ : Gate n T, (X γ S * X γ S') ^ 2)
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (C ^ 2 * (Q ^ 2 / Fintype.card (L3 I)))
      ≤ (m : ℝ) * C ^ (m - 1) * (C * Q)
        + ((m : ℝ) * m - m) * C ^ (m - 2) * (C ^ 2 * (Q ^ 2 / Fintype.card (L3 I))) := by
        gcongr
    _ = C ^ m * (m * Q + ((m : ℝ) * m - m) * (Q ^ 2 / Fintype.card (L3 I))) := by
        rw [show (m : ℝ) * C ^ (m - 1) * (C * Q) = m * (C ^ (m - 1) * C) * Q by ring, p1,
          show ((m : ℝ) * m - m) * C ^ (m - 2) * (C ^ 2 * (Q ^ 2 / Fintype.card (L3 I)))
            = ((m : ℝ) * m - m) * (C ^ (m - 2) * C ^ 2) * (Q ^ 2 / Fintype.card (L3 I)) by ring,
          p2]
        ring
    _ ≤ C ^ m * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / Fintype.card (L3 I)) := by
        gcongr
        have : 0 ≤ Q ^ 2 / (Fintype.card (L3 I) : ℝ) := by positivity
        rw [mul_div_assoc]
        nlinarith

end CircuitMoments

section Family

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (z : Fin n → Bool)

local notation "X" => colVec T I z

lemma lvl3_const {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) :
    lvl3 (fun _ : ι → Bool => c) = 0 := by
  ext S
  rw [lvl3_apply]
  unfold fourier
  have hS : S.1 ≠ ∅ := by intro h; have := S.2; rw [h] at this; simp at this
  have : ∑ x : ι → Bool, c * chi S.1 x = c * ∑ x : ι → Bool, chi S.1 x := by rw [mul_sum]
  rw [this, sum_chi, if_neg hS]; simp

/-- Ordered off-diagonal pairs. -/
def offPairs (m : ℕ) : Finset (Fin m × Fin m) := univ.filter (fun p => p.1 ≠ p.2)

/-- `‖∑ᵢ αᵢ Xᵢ‖² = S₂ + Q_α` for `α ∈ {±1}^m`. -/
lemma norm_sum_sq (ω : Fin m → Gate n T) (α : Fin m → ℝ) (hα : ∀ i, α i = 1 ∨ α i = -1) :
    ‖∑ i, α i • X (ω i)‖ ^ 2
      = S2c T I z ω + ∑ p ∈ offPairs m, α p.1 * α p.2 * ⟪X (ω p.1), X (ω p.2)⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
  have hall : ∑ i, ∑ j, α i * (α j * ⟪X (ω i), X (ω j)⟫)
      = ∑ p : Fin m × Fin m, α p.1 * α p.2 * ⟪X (ω p.1), X (ω p.2)⟫ := by
    rw [← Finset.univ_product_univ, sum_product]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
  rw [hall, ← sum_filter_add_sum_filter_not univ (fun p : Fin m × Fin m => p.1 ≠ p.2)]
  rw [add_comm]
  congr 1
  unfold S2c
  have hdiag : univ.filter (fun p : Fin m × Fin m => ¬ p.1 ≠ p.2)
      = univ.image (fun i : Fin m => (i, i)) := by
    ext p; simp only [mem_filter, mem_univ, true_and, not_not, mem_image]
    constructor
    · intro h; exact ⟨p.1, by ext <;> simp [h]⟩
    · rintro ⟨i, rfl⟩; rfl
  rw [hdiag, sum_image (fun i _ j _ h => by simpa using congrArg Prod.fst h)]
  refine sum_congr rfl (fun i _ => ?_)
  rw [real_inner_self_eq_norm_sq]
  rcases hα i with h | h <;> rw [h] <;> ring

lemma sq_gram {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ) :
    ∑ i, ∑ j, (∑ S, a i S * a j S) ^ 2 = ∑ S, ∑ S', (∑ i, a i S * a i S') ^ 2 := by
  simp_rw [sq, sum_mul_sum]
  calc ∑ i, ∑ j, ∑ S, ∑ S', a i S * a j S * (a i S' * a j S')
      = ∑ i, ∑ S, ∑ j, ∑ S', a i S * a j S * (a i S' * a j S') :=
        sum_congr rfl (fun i _ => sum_comm)
    _ = ∑ i, ∑ S, ∑ S', ∑ j, a i S * a j S * (a i S' * a j S') :=
        sum_congr rfl (fun i _ => sum_congr rfl (fun S _ => sum_comm))
    _ = ∑ S, ∑ i, ∑ S', ∑ j, a i S * a j S * (a i S' * a j S') := sum_comm
    _ = ∑ S, ∑ S', ∑ i, ∑ j, a i S * a j S * (a i S' * a j S') :=
        sum_congr rfl (fun S _ => sum_comm)
    _ = ∑ S, ∑ S', ∑ i, ∑ j, a i S * a i S' * (a j S * a j S') :=
        sum_congr rfl (fun S _ => sum_congr rfl (fun S' _ =>
          sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))))

/-- `∑_{i,j} ⟪Xᵢ,Xⱼ⟫² = U'`. -/
lemma sum_inner_sq (ω : Fin m → Gate n T) :
    ∑ p : Fin m × Fin m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2 = Ux T I z ω := by
  unfold Ux
  rw [← Finset.univ_product_univ, sum_product]
  have h := sq_gram (fun (i : Fin m) (S : L3 I) => X (ω i) S)
  rw [← h]
  refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
  congr 1
  rw [PiLp.inner_apply]
  exact sum_congr rfl (fun S _ => by simp [mul_comm])

/-- Fourth-moment identity for a 4-wise independent `±1` family. -/
lemma sum_family_Q_sq (ω : Fin m → Gate n T) {K : ℕ} (A : Fin K → Fin m → ℝ)
    (hA : ∀ a i, A a i = 1 ∨ A a i = -1)
    (h4 : ∀ i j k l : Fin m, i ≠ j → k ≠ l → ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∑ a, A a i * A a j * A a k * A a l = 0) :
    ∑ a, (∑ p ∈ offPairs m, A a p.1 * A a p.2 * ⟪X (ω p.1), X (ω p.2)⟫) ^ 2
      = 2 * K * ∑ p ∈ offPairs m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2 := by
  set g : Fin m × Fin m → ℝ := fun p => ⟪X (ω p.1), X (ω p.2)⟫ with hg
  have hsymm : ∀ p : Fin m × Fin m, g p.swap = g p := fun p => real_inner_comm _ _
  have hsq1 : ∀ a i, A a i * A a i = 1 := fun a i => by
    rcases hA a i with h | h <;> rw [h] <;> norm_num
  have hcoef : ∀ p ∈ offPairs m, ∀ q ∈ offPairs m,
      ∑ a, A a p.1 * A a p.2 * (A a q.1 * A a q.2)
        = (K : ℝ) * ((if q = p then 1 else 0) + (if q = p.swap then 1 else 0)) := by
    intro p hp q hq
    simp only [offPairs, mem_filter, mem_univ, true_and] at hp hq
    have hK : ∀ i j, ∑ a, A a i * A a j * (A a i * A a j) = (K : ℝ) := by
      intro i j
      rw [sum_congr rfl (fun a _ => show A a i * A a j * (A a i * A a j) = 1 by
        rw [show A a i * A a j * (A a i * A a j) = (A a i * A a i) * (A a j * A a j) by ring,
          hsq1, hsq1, one_mul])]
      simp
    by_cases h1 : q = p
    · subst h1
      have : q ≠ q.swap := fun h => hq (by simpa using congrArg Prod.fst h)
      rw [hK, if_pos rfl, if_neg this]; ring
    by_cases h2 : q = p.swap
    · subst h2
      have e : ∑ a, A a p.1 * A a p.2 * (A a p.swap.1 * A a p.swap.2) = (K : ℝ) := by
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [sum_congr rfl (fun a _ => show A a p.1 * A a p.2 * (A a p.2 * A a p.1) = 1 by
          rw [show A a p.1 * A a p.2 * (A a p.2 * A a p.1) = (A a p.1 * A a p.1) * (A a p.2 * A a p.2)
            by ring, hsq1, hsq1, one_mul])]
        simp
      rw [e, if_neg h1, if_pos rfl]; ring
    · have hne : ¬ ((p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)) := by
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
        · exact h1 (Prod.ext e1.symm e2.symm)
        · exact h2 (Prod.ext (by simp [e2]) (by simp [e1]))
      have := h4 p.1 p.2 q.1 q.2 hp hq hne
      rw [if_neg h1, if_neg h2]
      rw [show ∑ a, A a p.1 * A a p.2 * (A a q.1 * A a q.2)
        = ∑ a, A a p.1 * A a p.2 * A a q.1 * A a q.2 from sum_congr rfl (fun a _ => by ring), this]
      ring
  have hexp : ∀ a, (∑ p ∈ offPairs m, A a p.1 * A a p.2 * g p) ^ 2
      = ∑ p ∈ offPairs m, ∑ q ∈ offPairs m, (A a p.1 * A a p.2 * (A a q.1 * A a q.2)) * (g p * g q) := by
    intro a
    rw [sq, sum_mul_sum]
    exact sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => by ring))
  have hswap_mem : ∀ p ∈ offPairs m, p.swap ∈ offPairs m := by
    intro p hp
    simp only [offPairs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact Ne.symm hp
  show ∑ a, (∑ p ∈ offPairs m, A a p.1 * A a p.2 * g p) ^ 2
    = 2 * K * ∑ p ∈ offPairs m, g p ^ 2
  simp_rw [hexp]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl (fun p hp => ?_)
  rw [sum_comm]
  simp_rw [← sum_mul]
  rw [sum_congr rfl (fun q hq => by rw [hcoef p hp q hq])]
  simp only [mul_add, add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero]
  rw [sum_ite_eq' (offPairs m) p, sum_ite_eq' (offPairs m) p.swap, if_pos hp,
    if_pos (hswap_mem p hp), hsymm p]
  ring

/-- **Deterministic core of R3.** -/
theorem family_cert (ω : Fin m → Gate n T) {K : ℕ} (A : Fin K → Fin m → ℝ)
    (hA : ∀ a i, A a i = 1 ∨ A a i = -1)
    (h4 : ∀ i j k l : Fin m, i ≠ j → k ≠ l → ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∑ a, A a i * A a j * A a k * A a l = 0)
    (c : Fin K → ℝ) {W δ : ℝ} (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hS2 : 2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ≤ S2c T I z ω) :
    ((univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ)).card : ℝ)
        * S2c T I z ω ^ 2 ≤ 8 * K * Ux T I z ω := by
  classical
  set R2 : ℝ := W ^ 2 + 4 * δ * (m : ℝ) ^ 2 with hR2
  set Qa : Fin K → ℝ := fun a => ∑ p ∈ offPairs m, A a p.1 * A a p.2 * ⟪X (ω p.1), X (ω p.2)⟫
    with hQa
  have hS0 : 0 ≤ S2c T I z ω := by unfold S2c; positivity
  have hcert : ∀ a, certified T ω (A a) I z (fun _ => c a) W δ →
      S2c T I z ω ^ 2 / 4 ≤ Qa a ^ 2 := by
    intro a ha
    have hα : ∀ i, A a i = 1 ∨ A a i = -1 ∨ A a i = 0 := fun i => by
      rcases hA a i with h | h <;> simp [h]
    have hb := certified_ball T ω (A a) hα I z (fun _ => c a) hW hδ ha
    rw [lvl3_const, sub_zero] at hb
    have hb2 : ‖∑ i, A a i • X (ω i)‖ ^ 2 ≤ R2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rwa [Real.sq_sqrt (by positivity)] at this
    rw [norm_sum_sq T I z ω (A a) (hA a)] at hb2
    have hQ : Qa a ≤ -(S2c T I z ω / 2) := by
      rw [show Qa a = ∑ p ∈ offPairs m, A a p.1 * A a p.2 * ⟪X (ω p.1), X (ω p.2)⟫ from rfl]
      linarith
    nlinarith
  have hsum := sum_family_Q_sq T I z ω A hA h4
  have hU : ∑ p ∈ offPairs m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2 ≤ Ux T I z ω := by
    rw [← sum_inner_sq]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => sq_nonneg _)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  calc ((univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ)).card : ℝ)
        * S2c T I z ω ^ 2
      = 4 * ∑ a ∈ univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ),
          S2c T I z ω ^ 2 / 4 := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * ∑ a ∈ univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ),
          Qa a ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum
        intro a ha
        exact hcert a (by simpa using ha)
    _ ≤ 4 * ∑ a, Qa a ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => sq_nonneg _)
    _ = 4 * (2 * K * ∑ p ∈ offPairs m, ⟪X (ω p.1), X (ω p.2)⟫ ^ 2) := by
        rw [← hsum]
    _ ≤ 8 * K * Ux T I z ω := by nlinarith

end Family

section R3

variable {n m : ℕ} (T : Finset ℤ) [Nonempty T] (I : Finset (Fin n)) (W δ : ℝ)

/-- A column is *dangerous* for `ω` if some 4-wise independent `±1` family certifies it with
`y`-constant centers for at least half of its members. -/
def danger (ω : Fin m → Gate n T) (z : Fin n → Bool) : Prop :=
  ∃ (K : ℕ) (A : Fin K → Fin m → ℝ) (c : Fin K → ℝ), 0 < K ∧
    (∀ a i, A a i = 1 ∨ A a i = -1) ∧
    (∀ i j k l : Fin m, i ≠ j → k ≠ l → ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) →
      ∑ a, A a i * A a j * A a k * A a l = 0) ∧
    (K : ℝ) / 2 ≤ ((univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ)).card : ℝ)

/-- Good columns: `U'` and `S₂` are near their means. -/
def goodCol (ω : Fin m → Gate n T) (z : Fin n → Bool) : Prop :=
  Ux T I z ω ≤ 16 * (m * Qm T I z + (m : ℝ) ^ 2 * Qm T I z ^ 2 / Fintype.card (L3 I)) ∧
    m * Qm T I z / 2 ≤ S2c T I z ω

lemma good_not_danger (ω : Fin m → Gate n T) (z : Fin n → Bool) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hN : (2048 : ℝ) < Fintype.card (L3 I))
    (hQ : 4096 ≤ m * Qm T I z ∧ 8 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ≤ m * Qm T I z)
    (hg : goodCol T I ω z) : ¬ danger T I W δ ω z := by
  rintro ⟨K, A, c, hK, hA, h4, hhalf⟩
  obtain ⟨hU, hS⟩ := hg
  set Q := Qm T I z
  set N : ℝ := (Fintype.card (L3 I) : ℝ)
  have hmQ : 0 < (m : ℝ) * Q := by linarith [hQ.1]
  have hS2 : 2 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ≤ S2c T I z ω := by linarith [hQ.2]
  have hfc := family_cert T I z ω A hA h4 c hW hδ hS2
  set cnt : ℝ := ((univ.filter (fun a => certified T ω (A a) I z (fun _ => c a) W δ)).card : ℝ)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hS0 : 0 < S2c T I z ω := by linarith
  -- cnt * S2² ≤ 8K * 16 (mQ + m²Q²/N) and S2 ≥ mQ/2
  have h1 : cnt * (m * Q / 2) ^ 2 ≤ 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N)) := by
    have hc0 : 0 ≤ cnt := by positivity
    calc cnt * (m * Q / 2) ^ 2 ≤ cnt * S2c T I z ω ^ 2 := by
          gcongr
      _ ≤ 8 * K * Ux T I z ω := hfc
      _ ≤ 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N)) := by gcongr
  -- hence cnt ≤ 512 K (1/(mQ) + 1/N) < K/2
  have hNpos : 0 < N := by linarith
  have h2 : cnt ≤ 512 * K * (1 / (m * Q) + 1 / N) := by
    have hm0 : (m : ℝ) ≠ 0 := by intro h; rw [h] at hmQ; simp at hmQ
    have hQ0 : Q ≠ 0 := by intro h; rw [h] at hmQ; simp at hmQ
    have e : 8 * K * (16 * (m * Q + (m : ℝ) ^ 2 * Q ^ 2 / N))
        = 512 * K * (1 / (m * Q) + 1 / N) * (m * Q / 2) ^ 2 := by
      field_simp; ring
    rw [e] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have h3 : 512 * K * (1 / (m * Q) + 1 / N) < K / 2 := by
    have a1 : 1 / (m * Q) ≤ 1 / 4096 := one_div_le_one_div_of_le (by norm_num) hQ.1
    have a2 : 1 / N < 1 / 2048 := one_div_lt_one_div_of_lt (by norm_num) hN
    nlinarith
  linarith

open Classical in
/-- **Theorem R3** (fixed live set `I`). For at least half of all random circuits, fewer than a
quarter of the columns are dangerous: no 4-wise independent `±1` family (possibly chosen after
seeing the circuit and the column) certifies them, with `y`-constant centers, for half its members. -/
theorem layering_barrier (hm : 2 ≤ m) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (hN : (2048 : ℝ) < Fintype.card (L3 I))
    (hQ : ∀ z, 4096 ≤ m * Qm T I z ∧ 8 * (W ^ 2 + 4 * δ * (m : ℝ) ^ 2) ≤ m * Qm T I z) :
    ((univ.filter (fun ω : Fin m → Gate n T =>
        (2 : ℝ) ^ n / 4 ≤ ((univ.filter (fun z : Fin n → Bool =>
          danger T I W δ ω z)).card : ℝ))).card : ℝ)
      / (Fintype.card (Gate n T) : ℝ) ^ m ≤ 1 / 2 := by
  set G : ℝ := (Fintype.card (Gate n T) : ℝ) ^ m with hGdef
  have hG : 0 < G := by have := card_gate_pos T (n := n); positivity
  have hNpos : (0 : ℝ) < Fintype.card (L3 I) := by linarith
  have hNnat : 0 < Fintype.card (L3 I) := by exact_mod_cast hNpos
  -- per column: few circuits are bad
  have hbad : ∀ z : Fin n → Bool,
      ((univ.filter (fun ω : Fin m → Gate n T => ¬ goodCol T I ω z)).card : ℝ)
        ≤ G * (1 / 16 + 1 / 1024) := by
    intro z
    set Q := Qm T I z
    set B : ℝ := m * Q + (m : ℝ) ^ 2 * Q ^ 2 / Fintype.card (L3 I) with hB
    have hmQ : 4096 ≤ (m : ℝ) * Q := (hQ z).1
    have hBpos : 0 < B := by
      have : 0 ≤ (m : ℝ) ^ 2 * Q ^ 2 / Fintype.card (L3 I) := by positivity
      linarith
    have hU : ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)).card : ℝ)
        ≤ G / 16 := by
      have hsum := sum_Ux T I z hm hNnat
      rw [← hGdef] at hsum
      have : ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)).card : ℝ)
          * (16 * B) ≤ ∑ ω : Fin m → Gate n T, Ux T I z ω := by
        rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
        calc ∑ ω ∈ univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω),
              ((1 : ℕ) : ℝ) * (16 * B)
            ≤ ∑ ω ∈ univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω),
                Ux T I z ω := sum_le_sum (fun ω hω => by
                  simp only [mem_filter, mem_univ, true_and] at hω; push_cast; linarith)
          _ ≤ ∑ ω : Fin m → Gate n T, Ux T I z ω := by
              apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              intro ω _ _; unfold Ux; positivity
      have h16 : ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)).card : ℝ)
          * (16 * B) ≤ G * B := le_trans this hsum
      have : ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)).card : ℝ)
          * 16 ≤ G := by
        by_contra hc
        push Not at hc
        nlinarith [mul_lt_mul_of_pos_right hc hBpos]
      linarith
    have hS : ((univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2)).card : ℝ)
        ≤ G / 1024 := by
      have hvar := sum_S2c_var T I z hm
      rw [← hGdef] at hvar
      have : ((univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2)).card : ℝ)
          * (m * Q / 2) ^ 2 ≤ ∑ ω : Fin m → Gate n T, (S2c T I z ω - m * Q) ^ 2 := by
        rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
        calc ∑ ω ∈ univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2),
              ((1 : ℕ) : ℝ) * (m * Q / 2) ^ 2
            ≤ ∑ ω ∈ univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2),
                (S2c T I z ω - m * Q) ^ 2 := sum_le_sum (fun ω hω => by
                  simp only [mem_filter, mem_univ, true_and] at hω
                  have h0 : 0 ≤ S2c T I z ω := by unfold S2c; positivity
                  push_cast; nlinarith)
          _ ≤ ∑ ω : Fin m → Gate n T, (S2c T I z ω - m * Q) ^ 2 :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ω _ _ => sq_nonneg _)
      have h2 := le_trans this hvar
      have hmQpos : 0 < (m : ℝ) * Q := by linarith
      have : ((univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2)).card : ℝ)
          ≤ G * 4 / (m * Q) := by
        rw [le_div_iff₀ hmQpos]
        have e : (m * Q / 2) ^ 2 = (m * Q) * (m * Q) / 4 := by ring
        rw [e] at h2
        nlinarith
      calc _ ≤ G * 4 / (m * Q) := this
        _ ≤ G * 4 / 4096 := by gcongr
        _ = G / 1024 := by ring
    have hsub : univ.filter (fun ω : Fin m → Gate n T => ¬ goodCol T I ω z)
        ⊆ univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)
          ∪ univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2) := by
      intro ω hω
      simp only [mem_filter, mem_univ, true_and, mem_union, goodCol, not_and_or, not_le] at hω ⊢
      rcases hω with h | h
      · left; rw [hB]; linarith
      · right; exact h
    calc ((univ.filter (fun ω : Fin m → Gate n T => ¬ goodCol T I ω z)).card : ℝ)
        ≤ ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)
          ∪ univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ((univ.filter (fun ω : Fin m → Gate n T => 16 * B < Ux T I z ω)).card : ℝ)
          + ((univ.filter (fun ω : Fin m → Gate n T => S2c T I z ω < m * Q / 2)).card : ℝ) := by
          exact_mod_cast card_union_le _ _
      _ ≤ G / 16 + G / 1024 := by linarith
      _ = G * (1 / 16 + 1 / 1024) := by ring
  -- dangerous columns are bad columns
  have hdg : ∀ ω : Fin m → Gate n T,
      ((univ.filter (fun z : Fin n → Bool => danger T I W δ ω z)).card : ℝ)
        ≤ ((univ.filter (fun z : Fin n → Bool => ¬ goodCol T I ω z)).card : ℝ) := by
    intro ω
    exact_mod_cast card_le_card (fun z hz => by
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact fun hg => good_not_danger T I W δ ω z hW hδ hN (hQ z) hg hz)
  -- Markov over ω
  have hswap : ∑ ω : Fin m → Gate n T,
      ((univ.filter (fun z : Fin n → Bool => ¬ goodCol T I ω z)).card : ℝ)
        = ∑ z : Fin n → Bool,
          ((univ.filter (fun ω : Fin m → Gate n T => ¬ goodCol T I ω z)).card : ℝ) := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    exact sum_comm
  have htot : ∑ ω : Fin m → Gate n T,
      ((univ.filter (fun z : Fin n → Bool => danger T I W δ ω z)).card : ℝ)
        ≤ (2 : ℝ) ^ n * (G * (1 / 16 + 1 / 1024)) := by
    calc _ ≤ ∑ ω : Fin m → Gate n T,
          ((univ.filter (fun z : Fin n → Bool => ¬ goodCol T I ω z)).card : ℝ) :=
          sum_le_sum (fun ω _ => hdg ω)
      _ = _ := hswap
      _ ≤ ∑ _z : Fin n → Bool, G * (1 / 16 + 1 / 1024) := sum_le_sum (fun z _ => hbad z)
      _ = (2 : ℝ) ^ n * (G * (1 / 16 + 1 / 1024)) := by
          simp [Fintype.card_fun, Fintype.card_bool]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hmk : ((univ.filter (fun ω : Fin m → Gate n T =>
        (2 : ℝ) ^ n / 4 ≤ ((univ.filter (fun z : Fin n → Bool =>
          danger T I W δ ω z)).card : ℝ))).card : ℝ) * ((2 : ℝ) ^ n / 4)
      ≤ ∑ ω : Fin m → Gate n T,
        ((univ.filter (fun z : Fin n → Bool => danger T I W δ ω z)).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
    calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Fin m → Gate n T =>
          (2 : ℝ) ^ n / 4 ≤ ((univ.filter (fun z : Fin n → Bool =>
            danger T I W δ ω z)).card : ℝ)),
            ((univ.filter (fun z : Fin n → Bool => danger T I W δ ω z)).card : ℝ) :=
          sum_le_sum (fun ω hω => by
            simp only [mem_filter, mem_univ, true_and] at hω; push_cast; linarith)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ω _ _ => by positivity)
  rw [div_le_iff₀ hG]
  have := le_trans hmk htot
  nlinarith

end R3

section Concrete

variable {n m : ℕ}

/-- `E‖X‖² ≥ N · Pr[τ = 1] · f`. -/
lemma Qm_ge (I : Finset (Fin n)) (z : Fin n → Bool) (h : ℕ) (hh : 1 ≤ h)
    (hI : I.card = 2 * h + 3) :
    (Fintype.card (L3 I) : ℝ) * pAtom (Tset n) I z * (1 / (64 * (h : ℝ) * (h + 1) ^ 2))
      ≤ Qm (Tset n) I z := by
  classical
  set f : ℝ := 1 / (64 * (h : ℝ) * (h + 1) ^ 2)
  have hcardI : Fintype.card I = 2 * h + 3 := by simp [hI]
  set Θ := ({j // j ∉ I} → Bool) × Tset n
  have hC : (Fintype.card (Gate n (Tset n)) : ℝ) = (2 : ℝ) ^ Fintype.card I * Fintype.card Θ := by
    rw [Fintype.card_congr (splitGate (Tset n) I), Fintype.card_prod, Fintype.card_fun,
      Fintype.card_bool]; push_cast; ring
  have hΘ : (0 : ℝ) < Fintype.card Θ := by
    have : 0 < Fintype.card Θ := Fintype.card_pos
    exact_mod_cast this
  have hS : ∀ S : L3 I,
      (2 : ℝ) ^ Fintype.card I * ((univ.filter (fun θ : Θ => tau (Tset n) I z θ = 1)).card * f)
        ≤ ∑ γ : Gate n (Tset n), colVec (Tset n) I z γ S ^ 2 := by
    intro S
    have := gate_cross (Tset n) I z S S
    rw [if_pos rfl] at this
    rw [show ∑ γ : Gate n (Tset n), colVec (Tset n) I z γ S ^ 2
      = ∑ γ : Gate n (Tset n), colVec (Tset n) I z γ S * colVec (Tset n) I z γ S from
        sum_congr rfl (fun γ _ => sq _), this]
    gcongr
    rw [← sum_filter_add_sum_filter_not univ (fun θ : Θ => tau (Tset n) I z θ = 1)]
    have h1 : ((univ.filter (fun θ : Θ => tau (Tset n) I z θ = 1)).card : ℝ) * f
        ≤ ∑ θ ∈ univ.filter (fun θ : Θ => tau (Tset n) I z θ = 1),
          fourier (thrFun (tau (Tset n) I z θ)) S.1 ^ 2 := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum (fun θ hθ => ?_)
      simp only [mem_filter, mem_univ, true_and] at hθ
      rw [hθ]
      exact fourier_thr1_sq_ge h hh hcardI S.1 S.2
    have h2 : 0 ≤ ∑ θ ∈ univ.filter (fun θ : Θ => ¬ tau (Tset n) I z θ = 1),
        fourier (thrFun (tau (Tset n) I z θ)) S.1 ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  unfold Qm pAtom
  rw [le_div_iff₀ (card_gate_pos (Tset n)), hC]
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [sum_comm]
  calc (Fintype.card (L3 I) : ℝ) * ((univ.filter (fun θ : Θ => tau (Tset n) I z θ = 1)).card
          / Fintype.card Θ) * f * ((2 : ℝ) ^ Fintype.card I * Fintype.card Θ)
      = ∑ _S : L3 I, (2 : ℝ) ^ Fintype.card I *
          ((univ.filter (fun θ : Θ => tau (Tset n) I z θ = 1)).card * f) := by
        rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
    _ ≤ _ := sum_le_sum (fun S _ => hS S)

open Classical in
/-- **Theorem R3, instantiated.** -/
theorem layering_barrier_concrete (h : ℕ) (hh : 1 ≤ h) (I : Finset (Fin n))
    (hI : I.card = 2 * h + 3) (hN : 2048 < (2 * h + 3).choose 3) (hn : 7 ≤ n)
    (hm : (5800 : ℝ) * (4 * Nat.sqrt n + 5) * (n : ℝ) ^ 2 ≤ m)
    {W δ : ℝ} (hW0 : 0 ≤ W) (hWn : W ≤ n) (hδ0 : 0 ≤ δ) (hδ : 4 * δ * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        (2 : ℝ) ^ n / 4 ≤ ((univ.filter (fun z : Fin n → Bool =>
          danger (Tset n) I W δ ω z)).card : ℝ))).card : ℝ)
      / (Fintype.card (Gate n (Tset n)) : ℝ) ^ m ≤ 1 / 2 := by
  have hcardI : Fintype.card I = 2 * h + 3 := by simp [hI]
  have hNL : (Fintype.card (L3 I) : ℝ) = ((2 * h + 3).choose 3 : ℕ) := by
    rw [card_L3, hcardI]
  have hn7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (0 : ℝ) < 4 * Nat.sqrt n + 5 := by positivity
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  apply layering_barrier (Tset n) I W δ hm2 hW0 hδ0 (by rw [hNL]; exact_mod_cast hN)
  intro z
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
  -- m Q ≥ m N p f ≥ m p / 48 ≥ 5800 q n² · (3/(4q)) / 48 = 90.625 n²
  have key : (90 : ℝ) * (n : ℝ) ^ 2 ≤ m * Qm (Tset n) I z := by
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
  constructor
  · nlinarith
  · have : W ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hW0 hWn 2
    nlinarith

end Concrete

end

end ProblemQ
