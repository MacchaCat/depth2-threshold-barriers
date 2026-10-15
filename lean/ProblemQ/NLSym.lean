import ProblemQ.NLMain
import ProblemQ.Periodic

/-!
# Theorem NL-SYM (fixed mid-bit symmetric top gate), union over live sets

Same model as Theorem NL-U, but each list entry is a single `F₂`-polynomial of the gate vector
(degree `≤ d` for every point) and must output the **fixed** symmetric function
`SYM(u) = ⌊|u|/h⌋ mod 2` (for `h = 2^t`: `bit_t` of the number of firing gates).

The only change is the per-point bound: offset Smolensky at the median is replaced by Lemma PS
(`Periodic.periodic_smolensky`, agreement `≤ 0.93` once `≥ 2600 h²` private coins are free).
Everything else is `nl_gen`.
-/

open Finset BigOperators

namespace ProblemQ

noncomputable section

namespace NLU

variable {n : ℕ}

/-- Correctness of a fixed-SYM entry, as a Boolean. -/
def symP {m L : ℕ} (h : ℕ) (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → ZMod 2) :
    Fin L → (Fin n → Bool) → (Fin m → Bool) → Bool :=
  fun a y u => decide (P a y u = Periodic.bitAt h 0 (Smolensky.count u))

/-- Lemma PS gives the per-point bound `0.93`. -/
lemma pointBound_sym {m L d h : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → ZMod 2)
    (hP : ∀ a x, P a x ∈ Smolensky.V d) (hh : 1024 ≤ h) (hd : 200 * (d + 1) ≤ h)
    {F₀ : ℕ} (hF₀ : 2600 * h ^ 2 ≤ F₀) :
    PointBound (symP h P) F₀ (93 / 100) := by
  classical
  intro a y Pset u₀ hcard
  set e : Fin Pset.card ≃ Pset := Pset.equivFin.symm
  set c₀ := ((Smolensky.ones u₀).filter (fun g => g ∉ Pset)).card
  have hQ : (fun β => P a y (Smolensky.embed Pset e u₀ β)) ∈ Smolensky.V (F := Pset.card) d :=
    Smolensky.restrict_mem Pset e u₀ (hP a y)
  have hps := Periodic.periodic_smolensky hh hd (le_trans hF₀ hcard) c₀ hQ
  have hset : univ.filter (fun β : Fin Pset.card → Bool =>
        symP h P a y (Smolensky.embed Pset e u₀ β) = true)
      = univ.filter (fun β : Fin Pset.card → Bool =>
          P a y (Smolensky.embed Pset e u₀ β) = Periodic.bitAt h c₀ (Smolensky.ones β).card) := by
    ext β
    simp only [mem_filter, mem_univ, true_and, symP, decide_eq_true_eq, Smolensky.ones_embed]
    unfold Periodic.bitAt
    rw [zero_add]
  rw [hset]
  exact hps

open Classical in
/-- **Theorem NL-SYM** (union over all live sets of size `k`). If every entry of an oblivious list
of `L` polynomials of gate-degree `≤ d ≤ h/200 - 1` must compute the fixed bit `⌊|u|/h⌋ mod 2`
of the gate vector on all but a `δ` fraction of at least half of the columns of some live set,
then the circuit is rare. -/
theorem nl_sym {m L d h : ℕ} (P : Fin L → (Fin n → Bool) → (Fin m → Bool) → ZMod 2)
    (hP : ∀ a x, P a x ∈ Smolensky.V d) (hh : 1024 ≤ h) (hd : 200 * (d + 1) ≤ h)
    {k M s q F₀ : ℕ} {δ : ℝ}
    (hMs : 16 * M ^ 2 ≤ s) (hsk : M * s ≤ k) (hF₀ : 2600 * h ^ 2 ≤ F₀)
    (hF : (F₀ : ℝ) ≤ m * π₀ n / 2) (hδ0 : 0 ≤ δ) (hδM : δ * M ≤ 1 / 100)
    (hn' : 400 ≤ n - k) (hq : 20 * q ≤ n - k) :
    ((univ.filter (fun ω : Fin m → Gate n (Tset n) =>
        ∃ I : Finset (Fin n), I.card = k ∧ Succeeds (symP h P) δ ω I)).card : ℝ)
      ≤ (n.choose k : ℝ) * (50 / 3 * ((M * Real.exp (-(m * π₀ n / 16)) +
          (n.choose q : ℝ) * (L * (93 / 100 : ℝ) ^ M) ^ q) *
          (Fintype.card (Gate n (Tset n)) : ℝ) ^ m)) :=
  nl_gen (symP h P) (pointBound_sym P hP hh hd hF₀) (by norm_num) hMs hsk hF hδ0 hδM hn' hq

end NLU

end

end ProblemQ
