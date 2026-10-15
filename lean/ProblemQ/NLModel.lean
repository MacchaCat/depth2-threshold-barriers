import ProblemQ.NLPoint
import ProblemQ.Uniform

/-!
# Theorem NL-U, part 1: the {0,1}-input gate model and the two-level frame

Gates are `(w, t) ∈ {0,1}^n × T` with value `1[t ≤ Σ_{x_l = 1} ±1]` (signs from `w`); this is the
`{0,1}`-input model in which a coordinate equal to `0` contributes nothing.

For a live set `I`, a base point `x₀`, and disjoint blocks `A i ⊆ I`:
* block point `bpt i` = `x₀` with block `A i` flipped;
* rows `O` = coordinates `o ∉ I` with `x₀ o = 0`;
* row point `rpt o i` = `bpt i` with coordinate `o` set to `1`.

At `rpt o i` a gate computes `1[t ≤ c_i + ±w_o]`, where `c_i` (the sum at `bpt i`) does not involve
the row weights `w_o (o ∈ O)`. A gate is *sensitive* at block `i` if `t - c_i ∈ {0, 1}`; then its
value at every row point `rpt o i` is the fresh coin `w_o`, otherwise it is a constant.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ}

/-- `±1` from a bit. -/
def sg (b : Bool) : ℤ := if b then 1 else -1

/-- `{0,1}`-input linear form `Σ_{x_l = 1} sg(w_l)`. -/
def lin (w x : Fin n → Bool) : ℤ := ∑ l, if x l then sg (w l) else 0

/-- Gate value in the `{0,1}`-input model. -/
def gval (γ : Gate n (Tset n)) (x : Fin n → Bool) : Bool := decide ((γ.2 : ℤ) ≤ lin γ.1 x)

/-- Gate vector of a circuit at `x`. -/
def gvec {m : ℕ} (ω : Fin m → Gate n (Tset n)) (x : Fin n → Bool) : Fin m → Bool :=
  fun j => gval (ω j) x

section Frame

variable (I : Finset (Fin n)) (x₀ : Fin n → Bool) {M : ℕ} (A : Fin M → Finset (Fin n))

/-- Block point: `x₀` with block `A i` flipped. -/
def bpt (i : Fin M) : Fin n → Bool := fun l => if l ∈ A i then !x₀ l else x₀ l

/-- Rows: outside coordinates where `x₀` is `0`. -/
def rows : Finset (Fin n) := univ.filter (fun l => l ∉ I ∧ x₀ l = false)

/-- Row point. -/
def rpt (o : Fin n) (i : Fin M) : Fin n → Bool := Function.update (bpt x₀ A i) o true

variable {I x₀ A}

lemma bpt_row (hA : ∀ i, A i ⊆ I) {o : Fin n} (ho : o ∈ rows I x₀) (i : Fin M) :
    bpt x₀ A i o = false := by
  simp only [rows, mem_filter, mem_univ, true_and] at ho
  have : o ∉ A i := fun h => ho.1 (hA i h)
  simp [bpt, this, ho.2]

lemma lin_update_true (w x : Fin n → Bool) (o : Fin n) (hx : x o = false) :
    lin w (Function.update x o true) = lin w x + sg (w o) := by
  classical
  unfold lin
  rw [← Finset.add_sum_erase _ _ (mem_univ o), ← Finset.add_sum_erase _ _ (mem_univ o)]
  rw [Function.update_self, hx]
  simp only [if_true, Bool.false_eq_true, if_false, zero_add]
  rw [add_comm]
  congr 1
  refine sum_congr rfl (fun l hl => ?_)
  rw [Function.update_of_ne (ne_of_mem_erase hl)]

lemma lin_rpt (hA : ∀ i, A i ⊆ I) {o : Fin n} (ho : o ∈ rows I x₀) (i : Fin M)
    (w : Fin n → Bool) :
    lin w (rpt x₀ A o i) = lin w (bpt x₀ A i) + sg (w o) :=
  lin_update_true w _ o (bpt_row hA ho i)

/-- Changing a weight at a coordinate where `x` is `0` does not change `lin`. -/
lemma lin_update_w (w x : Fin n → Bool) (o : Fin n) (hx : x o = false) (b : Bool) :
    lin (Function.update w o b) x = lin w x := by
  unfold lin
  refine sum_congr rfl (fun l _ => ?_)
  by_cases h : l = o
  · subst h; simp [hx]
  · rw [Function.update_of_ne h]

/-- Sensitivity of a gate at block `i`. -/
def sens (γ : Gate n (Tset n)) (i : Fin M) : Prop :=
  0 ≤ (γ.2 : ℤ) - lin γ.1 (bpt x₀ A i) ∧ (γ.2 : ℤ) - lin γ.1 (bpt x₀ A i) ≤ 1

instance (γ : Gate n (Tset n)) (i : Fin M) : Decidable (sens (x₀ := x₀) (A := A) γ i) := by
  unfold sens; infer_instance

lemma gval_key (t c : ℤ) (b : Bool) :
    decide (t ≤ c + (if b = true then 1 else -1))
      = if (0 ≤ t - c ∧ t - c ≤ 1) then b else decide (t ≤ c - 1) := by
  by_cases h : 0 ≤ t - c ∧ t - c ≤ 1
  · rw [if_pos h]
    cases b
    · simp only [Bool.false_eq_true, if_false]; apply decide_eq_false; omega
    · simp only [if_true]; apply decide_eq_true; omega
  · rw [if_neg h]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      (apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega)

/-- Value of a gate at a row point. -/
lemma gval_rpt (hA : ∀ i, A i ⊆ I) {o : Fin n} (ho : o ∈ rows I x₀) (i : Fin M)
    (γ : Gate n (Tset n)) :
    gval γ (rpt x₀ A o i) =
      if sens (x₀ := x₀) (A := A) γ i then γ.1 o
      else decide ((γ.2 : ℤ) ≤ lin γ.1 (bpt x₀ A i) - 1) := by
  unfold gval
  rw [lin_rpt hA ho i]
  unfold sens sg
  convert gval_key (γ.2 : ℤ) (lin γ.1 (bpt x₀ A i)) (γ.1 o) using 2

end Frame

end NLU

end

end ProblemQ
