module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovariancePhysical
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Scalar differentiation and transport cancellation for the covariance quadratic form -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open scoped BigOperators

/-- Scalar representation of the covariance quadratic form. -/
theorem qform_eq_scalar {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (s : ℝ) (y V : PDE.Vec d) :
    qform lam h s y V =
      (covarianceVV lam h s * PDE.vecDot y y -
        2 * covarianceXV lam h s * PDE.vecDot y V +
        covarianceXX lam h s * PDE.vecDot V V) / covarianceDet lam h s := by
  unfold qform
  rw [gramian_inv_blocks lam hh]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Scalar representation of the velocity component of inverse covariance. -/
theorem pform_eq_scalar {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (s : ℝ) (y V : PDE.Vec d) :
    pform lam h s y V =
      (-covarianceXV lam h s / covarianceDet lam h s) • y +
        (covarianceXX lam h s / covarianceDet lam h s) • V := by
  unfold pform
  rw [gramian_inv_blocks lam hh]
  simp

/-- Bilinearity of the explicit native Euclidean dot product under scalar multiplication. -/
theorem vecDot_smul_smul {d : ℕ} (a b : ℝ) (y V : PDE.Vec d) :
    PDE.vecDot (a • y) (b • V) = a * b * PDE.vecDot y V := by
  unfold PDE.vecDot
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Squared Euclidean norm of the inverse velocity component. -/
theorem vecNormSq_pform {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (s : ℝ) (y V : PDE.Vec d) :
    PDE.vecNormSq (pform lam h s y V) =
      (covarianceXV lam h s ^ 2 * PDE.vecDot y y -
        2 * covarianceXV lam h s * covarianceXX lam h s * PDE.vecDot y V +
        covarianceXX lam h s ^ 2 * PDE.vecDot V V) / covarianceDet lam h s ^ 2 := by
  rw [pform_eq_scalar lam hh, PDE.vecNormSq_add_expand,
    PDE.vecNormSq_smul, PDE.vecNormSq_smul, vecDot_smul_smul]
  unfold PDE.vecNormSq
  ring

/-- Derivative of a native dot product along a position line. -/
theorem hasDerivAt_vecDot_line {d : ℕ} (y V W : PDE.Vec d) (r : ℝ) :
    HasDerivAt (fun t => PDE.vecDot (y + t • V) W) (PDE.vecDot V W) r := by
  have hp := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (((hasDerivAt_id r).mul_const (V i)).const_add (y i)).mul_const (W i))
  convert hp using 1
  · funext t
    simp [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp [PDE.vecDot]

/-- Derivative of the squared native norm along a position line. -/
theorem hasDerivAt_vecDot_line_self {d : ℕ} (y V : PDE.Vec d) (r : ℝ) :
    HasDerivAt (fun t => PDE.vecDot (y + t • V) (y + t • V))
      (2 * PDE.vecDot V (y + r • V)) r := by
  have hp := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    ((((hasDerivAt_id r).mul_const (V i)).const_add (y i)).pow 2))
  convert hp using 1
  · funext t
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Pi.pow_apply, id_eq]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [PDE.vecDot, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Time derivative of the physical covariance quadratic form. -/
theorem hasDerivAt_qform_time {d : ℕ} {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs : -(h / 128) ≤ s) (y V : PDE.Vec d) :
    HasDerivAt (fun t => qform lam h t y V)
      (((lam * PDE.vecDot y y - 2 * covarianceVV lam h s * PDE.vecDot y V +
          2 * covarianceXV lam h s * PDE.vecDot V V) * covarianceDet lam h s -
        (covarianceVV lam h s * PDE.vecDot y y -
          2 * covarianceXV lam h s * PDE.vecDot y V +
          covarianceXX lam h s * PDE.vecDot V V) * (lam * covarianceXX lam h s)) /
        covarianceDet lam h s ^ 2) s := by
  have hn := (((hasDerivAt_covarianceVV lam h s).mul_const (PDE.vecDot y y)).sub
    ((hasDerivAt_covarianceXV lam h s).const_mul (2 * PDE.vecDot y V))).add
    ((hasDerivAt_covarianceXX lam h s).mul_const (PDE.vecDot V V))
  have hp := hn.div (hasDerivAt_covarianceDet lam h s) (covarianceDet_pos hlam hh hs).ne'
  convert hp using 1
  · funext t
    rw [qform_eq_scalar lam hh]
    congr 1
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- Position transport derivative of the covariance quadratic form. -/
theorem hasDerivAt_qform_transport {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (s : ℝ) (y V : PDE.Vec d) :
    HasDerivAt (fun (r : ℝ) => qform lam h s (y + r • V) V)
      ((2 * covarianceVV lam h s * PDE.vecDot V y -
        2 * covarianceXV lam h s * PDE.vecDot V V) / covarianceDet lam h s) 0 := by
  have hp := (((hasDerivAt_vecDot_line_self y V 0).const_mul
    (covarianceVV lam h s)).sub ((hasDerivAt_vecDot_line y V V 0).const_mul
    (2 * covarianceXV lam h s))).add (hasDerivAt_const 0
      (covarianceXX lam h s * PDE.vecDot V V))
  have hd := hp.div_const (covarianceDet lam h s)
  convert hd using 1
  · funext r
    rw [qform_eq_scalar lam hh]
    congr 1
  · simp only [zero_smul, add_zero]
    ring

/-- The time and transport terms cancel, leaving exactly the velocity diffusion square. -/
theorem quadratic_transport_identity {d : ℕ}
    (lam h sigma : ℝ) (hlam : 0 < lam) (hh : 0 < h)
    (hsigma : -(h / 128) < sigma) (y V : PDE.Vec d) :
    deriv (fun s => qform lam h s y V) sigma +
      deriv (fun (r : ℝ) => qform lam h sigma (y + r • V) V) 0 =
        -lam * PDE.vecNormSq (pform lam h sigma y V) := by
  rw [(hasDerivAt_qform_time hlam hh hsigma.le y V).deriv,
    (hasDerivAt_qform_transport lam hh sigma y V).deriv, vecNormSq_pform lam hh]
  rw [PDE.vecDot_comm V y]
  have hd := (covarianceDet_pos hlam hh hsigma.le).ne'
  field_simp
  unfold covarianceDet
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
