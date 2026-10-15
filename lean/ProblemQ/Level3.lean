import ProblemQ.Gates

/-!
# The level-3 Fourier coefficient of `1[∑ sgn y ≥ 1]`

For `|ι| = 2h + 3` and `|S| = 3`:
`fourier (thrFun 1) S = -(centralBinom h / 4^h) / (4 (h+1))`,
and hence `fourier (thrFun 1) S ^ 2 ≥ 1 / (64 h (h+1)^2)` for `h ≥ 1`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of `true` entries. -/
def nTrue (b : α → Bool) : ℕ := (univ.filter (fun j => b j = true)).card

lemma sum_sgn_eq (b : α → Bool) :
    ∑ j, sgn (b j) = 2 * (nTrue b : ℝ) - Fintype.card α := by
  rw [← sum_filter_add_sum_filter_not univ (fun j => b j = true)]
  have h1 : ∑ j ∈ univ.filter (fun j => b j = true), sgn (b j) = nTrue b := by
    rw [sum_congr rfl (fun j hj => by simp only [mem_filter] at hj; rw [hj.2, sgn_true])]
    simp [nTrue]
  have h2 : ∑ j ∈ univ.filter (fun j => ¬ b j = true), sgn (b j)
      = -((Fintype.card α : ℝ) - nTrue b) := by
    rw [sum_congr rfl (fun j hj => by
      simp only [mem_filter, Bool.not_eq_true] at hj; rw [hj.2, sgn_false])]
    rw [sum_const, nsmul_eq_mul, mul_neg_one, filter_not, card_sdiff_of_subset (filter_subset _ _)]
    simp [nTrue, Nat.cast_sub (card_le_univ _)]
  rw [h1, h2]; ring

lemma sum_fun_bool_nTrue (g : ℕ → ℝ) :
    ∑ b : α → Bool, g (nTrue b)
      = ∑ t ∈ range (Fintype.card α + 1), ((Fintype.card α).choose t : ℝ) * g t := by
  have := Finset.sum_powerset_apply_card g (x := (univ : Finset α))
  rw [card_univ] at this
  simp only [nsmul_eq_mul] at this
  rw [← this]
  refine Finset.sum_nbij' (fun b => univ.filter (fun j => b j = true))
    (fun T j => decide (j ∈ T)) ?_ ?_ ?_ ?_ ?_
  · intro b _; simp
  · intro T _; simp
  · intro b _; funext j; simp
  · intro T _; ext j; simp
  · intro b _; rfl

end Counting

lemma prod_sgn_eq {α : Type*} [Fintype α] [DecidableEq α] (a : α → Bool) :
    ∏ j, sgn (a j) = (-1 : ℝ) ^ (Fintype.card α - nTrue a) := by
  rw [← prod_filter_mul_prod_filter_not univ (fun j => a j = true)]
  have h1 : ∏ j ∈ univ.filter (fun j => a j = true), sgn (a j) = 1 :=
    prod_eq_one (fun j hj => by simp only [mem_filter] at hj; rw [hj.2, sgn_true])
  have h2 : ∏ j ∈ univ.filter (fun j => ¬ a j = true), sgn (a j)
      = (-1) ^ (Fintype.card α - nTrue a) := by
    rw [prod_congr rfl (fun j hj => by
      simp only [mem_filter, Bool.not_eq_true] at hj; rw [hj.2, sgn_false]), prod_const,
      filter_not, card_sdiff_of_subset (filter_subset _ _)]
    simp [nTrue]
  rw [h1, h2, one_mul]

/-- Pointwise collapse of the four-term alternating sum. -/
lemma psi_eq (h u : ℕ) (hh : 1 ≤ h) :
    ∑ t ∈ range 4, ((3 : ℕ).choose t : ℝ) * ((-1 : ℝ) ^ (3 - t) *
        (if (1 : ℝ) ≤ (2 * (t : ℝ) - 3) + (2 * (u : ℝ) - 2 * h) then 1 else 0))
      = (if u = h - 1 then 1 else 0) - 2 * (if u = h then 1 else 0)
        + (if u = h + 1 then 1 else 0) := by
  have key : ∀ t : ℕ, ((1 : ℝ) ≤ (2 * (t : ℝ) - 3) + (2 * (u : ℝ) - 2 * h)) ↔ h + 2 ≤ t + u := by
    intro t
    constructor
    · intro H
      have : ((h : ℝ) + 2) ≤ t + u := by linarith
      exact_mod_cast this
    · intro H
      have : ((h : ℝ) + 2) ≤ t + u := by exact_mod_cast H
      linarith
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, key]
  norm_num
  split_ifs <;> norm_num <;> omega

/-- **Level-3 coefficient of `1[∑ sgn ≥ 1]`.** -/
theorem fourier_thr1 {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ℕ) (hh : 1 ≤ h)
    (hcard : Fintype.card ι = 2 * h + 3) (S : Finset ι) (hS : S.card = 3) :
    fourier (thrFun 1) S
      = -((Nat.centralBinom h : ℝ) / 4 ^ h) / (4 * (h + 1)) := by
  classical
  set e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)
  have hcS : Fintype.card {i // i ∈ S} = 3 := by simp [hS]
  have hcR : Fintype.card {i // i ∉ S} = 2 * h := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hS, hcard]; omega
  -- rewrite the sum over the cube as a double sum
  have hsplit : ∑ y : ι → Bool, thrFun 1 y * chi S y
      = ∑ a : {i // i ∈ S} → Bool, ∑ b : {i // i ∉ S} → Bool,
          (if (1 : ℝ) ≤ (2 * (nTrue a : ℝ) - 3) + (2 * (nTrue b : ℝ) - 2 * h) then 1 else 0)
            * (-1 : ℝ) ^ (3 - nTrue a) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    congr! 2 with a _ b _
    have hS' : ∀ i : {i // i ∈ S}, e.symm (a, b) i = a i := fun i => by
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
    have hR' : ∀ i : {i // i ∉ S}, e.symm (a, b) i = b i := fun i => by
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
    have hsum : ∑ j, sgn (e.symm (a, b) j)
        = ∑ i : {i // i ∈ S}, sgn (a i) + ∑ i : {i // i ∉ S}, sgn (b i) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S)]
      simp only [hS', hR']
      congr 1
      exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
    have hchi : chi S (e.symm (a, b)) = ∏ i : {i // i ∈ S}, sgn (a i) := by
      unfold chi
      rw [← Finset.prod_coe_sort S]
      simp only [hS']
    rw [hchi, prod_sgn_eq, hcS]
    unfold thrFun
    rw [hsum, sum_sgn_eq, sum_sgn_eq, hcS, hcR]
    push_cast
    ring_nf
  have hcount : ∑ y : ι → Bool, thrFun 1 y * chi S y
      = ((2 * h).choose (h - 1) : ℝ) - 2 * ((2 * h).choose h : ℝ)
        + ((2 * h).choose (h + 1) : ℝ) := by
    rw [hsplit, sum_comm]
    have inner : ∀ b : {i // i ∉ S} → Bool,
        ∑ a : {i // i ∈ S} → Bool,
          (if (1 : ℝ) ≤ (2 * (nTrue a : ℝ) - 3) + (2 * (nTrue b : ℝ) - 2 * h) then 1 else 0)
            * (-1 : ℝ) ^ (3 - nTrue a)
        = (if nTrue b = h - 1 then 1 else 0) - 2 * (if nTrue b = h then 1 else 0)
            + (if nTrue b = h + 1 then 1 else 0) := by
      intro b
      rw [sum_fun_bool_nTrue (fun t => (if (1 : ℝ) ≤ (2 * (t : ℝ) - 3)
          + (2 * (nTrue b : ℝ) - 2 * h) then 1 else 0) * (-1 : ℝ) ^ (3 - t)), hcS]
      rw [← psi_eq h (nTrue b) hh]
      exact sum_congr rfl (fun t _ => by ring)
    rw [sum_congr rfl (fun b _ => inner b)]
    rw [sum_fun_bool_nTrue (fun u => (if u = h - 1 then (1 : ℝ) else 0)
        - 2 * (if u = h then 1 else 0) + (if u = h + 1 then 1 else 0)), hcR]
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq', sum_ite_eq', sum_ite_eq']
    simp only [mem_range]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
    ring
  -- binomial identities
  have hsym : (2 * h).choose (h - 1) = (2 * h).choose (h + 1) := by
    rw [← Nat.choose_symm (by omega : h - 1 ≤ 2 * h)]
    congr 1; omega
  have hsucc : ((2 * h).choose (h + 1) : ℝ) * (h + 1) = ((2 * h).choose h : ℝ) * h := by
    have := Nat.choose_succ_right_eq (2 * h) h
    have h2 : 2 * h - h = h := by omega
    rw [h2] at this
    exact_mod_cast this
  unfold fourier
  rw [hcount, hsym, hcard, Nat.centralBinom_eq_two_mul_choose]
  have hpos : (0 : ℝ) < h + 1 := by positivity
  have : ((2 * h).choose (h + 1) : ℝ) = ((2 * h).choose h : ℝ) * h / (h + 1) := by
    rw [eq_div_iff hpos.ne']; exact hsucc
  rw [this]
  field_simp
  rw [show (4 : ℝ) ^ h = 2 ^ (2 * h) by rw [pow_mul]; norm_num]
  push_cast
  ring

/-- `(centralBinom h / 4^h)^2 ≥ 1/(4h)` for `h ≥ 1`. -/
lemma centralBinom_sq_ge (h : ℕ) (hh : 1 ≤ h) :
    1 / (4 * (h : ℝ)) ≤ ((Nat.centralBinom h : ℝ) / 4 ^ h) ^ 2 := by
  induction h with
  | zero => omega
  | succ h ih =>
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · norm_num [Nat.centralBinom]
    · have ih := ih hpos
      have hrec : ((h : ℝ) + 1) * Nat.centralBinom (h + 1) = 2 * (2 * h + 1) * Nat.centralBinom h := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ h
      have hc : (Nat.centralBinom (h + 1) : ℝ) / 4 ^ (h + 1)
          = (Nat.centralBinom h : ℝ) / 4 ^ h * ((2 * h + 1) / (2 * h + 2)) := by
        have hne : ((h : ℝ) + 1) ≠ 0 := by positivity
        have : (Nat.centralBinom (h + 1) : ℝ) = 2 * (2 * h + 1) * Nat.centralBinom h / (h + 1) := by
          rw [eq_div_iff hne, mul_comm]; exact hrec
        rw [this, pow_succ]
        field_simp
        ring
      rw [hc, mul_pow]
      have hh' : (0 : ℝ) < h := by exact_mod_cast hpos
      have key : 1 / (4 * ((h : ℝ) + 1)) ≤ 1 / (4 * h) * ((2 * h + 1) / (2 * h + 2)) ^ 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      push_cast
      calc 1 / (4 * ((h : ℝ) + 1)) ≤ 1 / (4 * h) * ((2 * h + 1) / (2 * h + 2)) ^ 2 := key
        _ ≤ ((Nat.centralBinom h : ℝ) / 4 ^ h) ^ 2 * ((2 * h + 1) / (2 * h + 2)) ^ 2 := by
            gcongr

/-- Lower bound on the squared level-3 coefficient. -/
theorem fourier_thr1_sq_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ℕ) (hh : 1 ≤ h)
    (hcard : Fintype.card ι = 2 * h + 3) (S : Finset ι) (hS : S.card = 3) :
    1 / (64 * (h : ℝ) * (h + 1) ^ 2) ≤ fourier (thrFun 1) S ^ 2 := by
  rw [fourier_thr1 h hh hcard S hS, neg_div, neg_sq, div_pow]
  have := centralBinom_sq_ge h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  rw [le_div_iff₀ (by positivity)]
  calc 1 / (64 * (h : ℝ) * (h + 1) ^ 2) * (4 * (h + 1)) ^ 2 = 1 / (4 * h) := by
        field_simp; ring
    _ ≤ _ := this

end

end ProblemQ
