module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlock
import Mathlib.Tactic

/-! # Gaussian height estimates for source overlap induction -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Before the block starts its positive Gaussian height is at most the source loss factor. -/
theorem gaussianBarrier_initial_upper {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    (hLam : lam ≤ Lam) (hell : 0 ≤ ell)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (_ht : P.time - tminus - sblock ≤ 0) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v P ≤
      ell * Real.exp (L ^ 2 / 512) := by
  by_cases hp : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P
  · have hs := (gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
      hLam hell hbudget x v P hp).1
    have hq := qform_nonneg hlam hh hs.le
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))
    have hXi := Xi_nonneg d (H := H) hlam hLam hh
    have htime := mul_le_mul_of_nonneg_left hs.le hXi
    have hexp : Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ≤
        Real.exp (L ^ 2 / 512) := by
      apply Real.exp_le_exp.mpr
      linarith only [htime, hbudget, hq]
    rw [gaussianBarrier_eq_formula]
    dsimp only [gaussianFormula]
    have hc := barrierCutoff_bounds ((P.time - tminus - sblock) / h)
    have hg : 0 ≤ Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) -
        Real.exp (-L ^ 2) := by
      rw [gaussianBarrier_eq_formula] at hp
      dsimp only [gaussianFormula] at hp
      exact (pos_of_mul_pos_right hp (mul_nonneg hell hc.1)).le
    calc
      _ ≤ ell * (Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
          qform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) -
          Real.exp (-L ^ 2)) := by
        have he := mul_le_mul_of_nonneg_right hc.2 hell
        nlinarith only [mul_le_mul_of_nonneg_right he hg]
      _ ≤ ell * Real.exp (L ^ 2 / 512) :=
        mul_le_mul_of_nonneg_left
          ((sub_le_self _ (Real.exp_pos _).le).trans hexp) hell
  · exact (le_of_not_gt hp).trans (mul_nonneg hell (Real.exp_pos _).le)

/-- In the terminal half-height ellipsoid the Gaussian dominates the source block height. -/
theorem gaussianBarrier_terminal_lower {d : ℕ} {lam h : ℝ}
    (hh : 0 < h) (Lam H L ell tminus sblock : ℝ) (hell : 0 ≤ ell)
    (hXi : 0 ≤ Xi d lam Lam H h) (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hs : 0 ≤ P.time - tminus - sblock) (ht : P.time - tminus - sblock ≤ h)
    (hq : qform lam h (P.time - tminus - sblock)
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2) :
    ell * barrierCb L ≤ gaussianBarrier lam Lam H h L ell tminus sblock x v P := by
  rw [gaussianBarrier_eq_formula]
  dsimp only [gaussianFormula]
  rw [barrierCutoff_one (div_nonneg hs hh.le), mul_one]
  apply mul_le_mul_of_nonneg_left _ hell
  unfold barrierCb
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have he := (mul_le_mul_of_nonneg_left ht hXi).trans hbudget
  linarith only [he, hq]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
