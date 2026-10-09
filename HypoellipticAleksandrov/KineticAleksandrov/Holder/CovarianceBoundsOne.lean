module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsFinal
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Sharp source covariance lower bound at one full block -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open scoped MatrixOrder

/-- At one full block, covariance dominates the source constant lambda/16. -/
theorem ghat_one_lower {lam : ℝ} (hlam : 0 < lam) :
    (lam / 16 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ ghat lam 1 := by
  have hunit : (1 / 16 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ ghat 1 1 := by
    apply Matrix.le_iff.mpr
    have hp := posDef_two_of_det
      (a := (29 / 96 : ℝ)) (b := (61 / 64 : ℝ)) (c := (33 / 64 : ℝ))
      (by norm_num) (by norm_num)
    convert hp.posSemidef using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ghat, Matrix.sub_apply, Matrix.smul_apply]
  have h := covariance_smul_le hunit hlam.le
  rw [ghat_smul lam 1]
  simpa only [smul_smul, div_eq_mul_inv, one_mul] using h

end HypoellipticAleksandrov.KineticAleksandrov.Holder
