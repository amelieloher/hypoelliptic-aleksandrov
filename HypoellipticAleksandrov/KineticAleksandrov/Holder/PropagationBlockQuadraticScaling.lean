module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculus
import Mathlib.Tactic

/-! # Exact dimensionless rescaling of the native kinetic covariance quadratic -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

/-- The physical dilation inverse is the literal reciprocal diagonal. -/
theorem covarianceDilation_inv {h : ℝ} (hh : 0 < h) :
    (covarianceDilation h)⁻¹ =
      !![(h ^ (3 / 2 : ℝ))⁻¹, 0; 0, (h ^ (1 / 2 : ℝ))⁻¹] := by
  have h3 := (Real.rpow_pos_of_pos hh (3 / 2 : ℝ)).ne'
  have h1 := (Real.rpow_pos_of_pos hh ((2 : ℝ)⁻¹)).ne'
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two, Ring.inverse_eq_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [covarianceDilation, Matrix.smul_apply, h3]
  field_simp [h1]

/-- The source quadratic is exactly the dimensionless inverse quadratic at scaled coordinates. -/
theorem qform_eq_dimensionless {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (y V : PDE.Vec d) :
    qform lam h sigma y V = blockQuadratic (ghat lam (sigma / h))⁻¹
      ((h ^ (3 / 2 : ℝ))⁻¹ • y) ((h ^ (1 / 2 : ℝ))⁻¹ • V) := by
  unfold qform gramian
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, covarianceDilation_inv hh]
  unfold blockQuadratic
  rw [vecDot_smul_smul, vecDot_smul_smul, vecDot_smul_smul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- Scalar multiplication of a definite block inverse has the expected reciprocal factor. -/
theorem covariance_inv_smul {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  let u : ℝˣ := Units.mk0 c hc.ne'
  have hu : (u : ℝ) = c := rfl
  have h := Matrix.inv_smul' M u (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  simpa only [Units.smul_def, hu, Units.val_inv_eq_inv_val] using h

/-- Multiplying the inverse of a positive scalar identity cancels that scalar. -/
theorem covariance_scalar_one_inv {c : ℝ} (hc : 0 < c) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa only [inv_one] using covariance_inv_smul Matrix.PosDef.one hc

end HypoellipticAleksandrov.KineticAleksandrov.Holder
