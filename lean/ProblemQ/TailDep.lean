import Mathlib

/-!
# Tail dependence of halfspaces

Rare *coordinated* firing of several halfspaces forces their normal vectors to be nearly
parallel. This is the rigorous core of the heuristic ("rare jumps must come from
near-parallel blocks, which are visible in the weight matrix").

Everything is stated by counting points of the cube `{±1}^k` (encoded as `Fin k → Bool`), with no
regularity assumption on the weights.

* `card_ge_le` (**Hoeffding, counting form**): for `T ≥ 0` and `‖a‖² > 0`,
  `#{y | T ≤ ⟨a, y⟩} ≤ 2^k · exp(−T² / (2‖a‖²))`.
* `card_all_ge_le` (**group tail dependence**): if all `G` halfspaces `⟨aᵢ, y⟩ ≥ tᵢ` hold, then so
  does `⟨∑ aᵢ, y⟩ ≥ ∑ tᵢ`, hence
  `#{y | ∀ i, tᵢ ≤ ⟨aᵢ, y⟩} ≤ 2^k · exp(−(∑ tᵢ)² / (2‖∑ aᵢ‖²))`.
* `pair_corr_ge` (**pairs**): for unit vectors `a, b` with `ρ = ⟨a, b⟩`, if both `⟨a,y⟩ ≥ t` and
  `⟨b,y⟩ ≥ t` hold on a fraction `p > 0` of the cube, then `t² ≤ (1 + ρ) · log (1/p)`.
-/

open Finset Real

namespace ProblemQ

namespace TailDep

variable {k : ℕ}

/-- The `±1` value of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The linear form `⟨a, y⟩` on the `±1` cube. -/
def lin (a : Fin k → ℝ) (y : Fin k → Bool) : ℝ := ∑ i, a i * sgn (y i)

/-- Squared Euclidean norm. -/
def nsq (a : Fin k → ℝ) : ℝ := ∑ i, a i ^ 2

lemma nsq_nonneg (a : Fin k → ℝ) : 0 ≤ nsq a := sum_nonneg (fun _ _ => sq_nonneg _)

/-- Exponential moment of `⟨a, y⟩` over the cube, as a product over coordinates. -/
lemma sum_exp_lin (a : Fin k → ℝ) (l : ℝ) :
    ∑ y : Fin k → Bool, exp (l * lin a y) = ∏ i, (exp (l * a i) + exp (-(l * a i))) := by
  have h : ∀ y : Fin k → Bool, exp (l * lin a y) = ∏ i, exp (l * (a i * sgn (y i))) := by
    intro y
    rw [lin, mul_sum, exp_sum]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun i (b : Bool) => exp (l * (a i * sgn b)))]
  refine prod_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  simp [sgn, mul_neg, mul_one]

/-- `e^x + e^{-x} ≤ 2 e^{x²/2}`. -/
lemma exp_add_exp_neg_le (x : ℝ) : exp x + exp (-x) ≤ 2 * exp (x ^ 2 / 2) := by
  have h := cosh_le_exp_half_sq x
  rw [cosh_eq] at h
  linarith

/-- Exponential-moment bound: `∑_y e^{l⟨a,y⟩} ≤ 2^k e^{l²‖a‖²/2}`. -/
lemma sum_exp_lin_le (a : Fin k → ℝ) (l : ℝ) :
    ∑ y : Fin k → Bool, exp (l * lin a y) ≤ 2 ^ k * exp (l ^ 2 * nsq a / 2) := by
  rw [sum_exp_lin]
  calc ∏ i, (exp (l * a i) + exp (-(l * a i)))
      ≤ ∏ i : Fin k, (2 * exp ((l * a i) ^ 2 / 2)) :=
        prod_le_prod₀ (fun i _ => by positivity) (fun i _ => exp_add_exp_neg_le _)
    _ = 2 ^ k * exp (l ^ 2 * nsq a / 2) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← exp_sum, nsq,
          mul_sum, sum_div]
        congr 2
        refine sum_congr rfl (fun i _ => ?_)
        ring

/-- **Hoeffding, counting form.** For `T ≥ 0` and `‖a‖² > 0`,
`#{y | T ≤ ⟨a,y⟩} ≤ 2^k · exp(−T²/(2‖a‖²))`. -/
theorem card_ge_le (a : Fin k → ℝ) (ha : 0 < nsq a) {T : ℝ} (hT : 0 ≤ T) :
    ((univ.filter (fun y : Fin k → Bool => T ≤ lin a y)).card : ℝ)
      ≤ 2 ^ k * exp (-(T ^ 2 / (2 * nsq a))) := by
  set l := T / nsq a with hl
  have hl0 : 0 ≤ l := div_nonneg hT ha.le
  -- Markov: each point of the tail contributes at least `e^{lT}`.
  have hmark : ((univ.filter (fun y : Fin k → Bool => T ≤ lin a y)).card : ℝ) * exp (l * T)
      ≤ ∑ y : Fin k → Bool, exp (l * lin a y) := by
    calc ((univ.filter (fun y : Fin k → Bool => T ≤ lin a y)).card : ℝ) * exp (l * T)
        = ∑ _y ∈ univ.filter (fun y : Fin k → Bool => T ≤ lin a y), exp (l * T) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ univ.filter (fun y : Fin k → Bool => T ≤ lin a y), exp (l * lin a y) := by
          refine sum_le_sum (fun y hy => ?_)
          simp only [mem_filter, mem_univ, true_and] at hy
          exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hl0)
      _ ≤ ∑ y : Fin k → Bool, exp (l * lin a y) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (exp_pos _).le)
  have hm := le_trans hmark (sum_exp_lin_le a l)
  have hpos : 0 < exp (l * T) := exp_pos _
  have key : l ^ 2 * nsq a / 2 - l * T = -(T ^ 2 / (2 * nsq a)) := by
    rw [hl]; field_simp; ring
  calc ((univ.filter (fun y : Fin k → Bool => T ≤ lin a y)).card : ℝ)
      ≤ 2 ^ k * exp (l ^ 2 * nsq a / 2) / exp (l * T) := by
        rw [le_div_iff₀ hpos]; exact hm
    _ = 2 ^ k * exp (-(T ^ 2 / (2 * nsq a))) := by
        rw [mul_div_assoc, ← exp_sub, key]

/-- `lin` is additive in the weight vector. -/
lemma lin_sum {G : ℕ} (a : Fin G → Fin k → ℝ) (y : Fin k → Bool) :
    lin (fun i => ∑ g, a g i) y = ∑ g, lin (a g) y := by
  simp only [lin, sum_mul]
  exact sum_comm

/-- **Group tail dependence.** If `G` halfspaces `⟨a_g, y⟩ ≥ t_g` all hold, their sum does; so for
`∑ t_g ≥ 0` and `‖∑ a_g‖² > 0`,
`#{y | ∀ g, t_g ≤ ⟨a_g,y⟩} ≤ 2^k · exp(−(∑ t_g)² / (2‖∑ a_g‖²))`. -/
theorem card_all_ge_le {G : ℕ} (a : Fin G → Fin k → ℝ) (t : Fin G → ℝ)
    (hA : 0 < nsq (fun i => ∑ g, a g i)) (ht : 0 ≤ ∑ g, t g) :
    ((univ.filter (fun y : Fin k → Bool => ∀ g, t g ≤ lin (a g) y)).card : ℝ)
      ≤ 2 ^ k * exp (-((∑ g, t g) ^ 2 / (2 * nsq (fun i => ∑ g, a g i)))) := by
  refine le_trans ?_ (card_ge_le _ hA ht)
  have hsub : univ.filter (fun y : Fin k → Bool => ∀ g, t g ≤ lin (a g) y)
      ⊆ univ.filter (fun y : Fin k → Bool => ∑ g, t g ≤ lin (fun i => ∑ g, a g i) y) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    rw [lin_sum]
    exact sum_le_sum (fun g _ => hy g)
  exact_mod_cast card_le_card hsub

/-- Inner product. -/
def dot (a b : Fin k → ℝ) : ℝ := ∑ i, a i * b i

/-- `‖a + b‖² = ‖a‖² + 2⟨a,b⟩ + ‖b‖²`. -/
lemma nsq_add (a b : Fin k → ℝ) : nsq (fun i => a i + b i) = nsq a + 2 * dot a b + nsq b := by
  simp only [nsq, dot, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  ring

/-- **Pairs.** For unit vectors `a, b` with correlation `ρ = ⟨a,b⟩ > -1`, the joint tail at height
`t ≥ 0` has at most `2^k · exp(−t²/(1+ρ))` points. -/
theorem card_pair_le (a b : Fin k → ℝ) (ha : nsq a = 1) (hb : nsq b = 1) (hρ : -1 < dot a b)
    {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter (fun y : Fin k → Bool => t ≤ lin a y ∧ t ≤ lin b y)).card : ℝ)
      ≤ 2 ^ k * exp (-(t ^ 2 / (1 + dot a b))) := by
  have hn : nsq (fun i => a i + b i) = 2 * (1 + dot a b) := by
    rw [nsq_add, ha, hb]; ring
  have hpos : 0 < nsq (fun i => a i + b i) := by rw [hn]; linarith
  have hsub : univ.filter (fun y : Fin k → Bool => t ≤ lin a y ∧ t ≤ lin b y)
      ⊆ univ.filter (fun y : Fin k → Bool => t + t ≤ lin (fun i => a i + b i) y) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    have : lin (fun i => a i + b i) y = lin a y + lin b y := by
      simp only [lin, add_mul, sum_add_distrib]
    rw [this]; linarith [hy.1, hy.2]
  have h1 := card_ge_le (fun i => a i + b i) hpos (by linarith : 0 ≤ t + t)
  have h2 : (t + t) ^ 2 / (2 * nsq (fun i => a i + b i)) = t ^ 2 / (1 + dot a b) := by
    rw [hn]; have : (0 : ℝ) < 1 + dot a b := by linarith
    field_simp; ring
  rw [h2] at h1
  exact le_trans (by exact_mod_cast card_le_card hsub) h1

/-- **Coordination forces correlation.** If unit vectors `a, b` both exceed `t ≥ 0` on a fraction
`p > 0` of the cube, then `t² ≤ (1 + ρ) · log (1/p)`. -/
theorem pair_corr_ge (a b : Fin k → ℝ) (ha : nsq a = 1) (hb : nsq b = 1) (hρ : -1 < dot a b)
    {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p)
    (hjoint : p * 2 ^ k ≤ ((univ.filter (fun y : Fin k → Bool => t ≤ lin a y ∧ t ≤ lin b y)).card : ℝ)) :
    t ^ 2 ≤ (1 + dot a b) * Real.log (1 / p) := by
  have h := le_trans hjoint (card_pair_le a b ha hb hρ ht)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hpe : p ≤ exp (-(t ^ 2 / (1 + dot a b))) := by
    have := h; rw [mul_comm] at this
    exact le_of_mul_le_mul_left this h2k
  have hlog : Real.log p ≤ -(t ^ 2 / (1 + dot a b)) := by
    rw [← Real.log_exp (-(t ^ 2 / (1 + dot a b)))]
    exact Real.log_le_log hp hpe
  have hρ' : (0 : ℝ) < 1 + dot a b := by linarith
  rw [one_div, Real.log_inv]
  have : t ^ 2 / (1 + dot a b) ≤ -Real.log p := by linarith
  rwa [div_le_iff₀ hρ', mul_comm] at this

end TailDep

end ProblemQ
