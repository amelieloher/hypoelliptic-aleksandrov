module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Scalar block covariance for kinetic transport

All matrices here represent scalar blocks tensored with the identity on the native
Euclidean vector space. The covariance formula is literal, including negative times.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

/-- Rescaled covariance from the source's transport and velocity diffusion. -/
def ghat (lam theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![lam / 64 * (1 + theta ^ 2) + lam * theta ^ 3 / 3,
    lam / 64 * theta + lam * theta ^ 2 / 2;
    lam / 64 * theta + lam * theta ^ 2 / 2, lam / 64 + lam * theta]

/-- Kinetic scaling matrix for the covariance. -/
def covarianceDilation (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![h ^ (3 / 2 : ℝ), 0; 0, h ^ (1 / 2 : ℝ)]

/-- Physical covariance, as the exact rescaling of the dimensionless covariance. -/
def gramian (lam h sigma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  covarianceDilation h * ghat lam (sigma / h) * covarianceDilation h

/-- Covariance quadratic form in native position–velocity coordinates. -/
def qform {d : ℕ} (lam h sigma : ℝ) (y V : PDE.Vec d) : ℝ :=
  (gramian lam h sigma)⁻¹ 0 0 * PDE.vecDot y y +
    2 * (gramian lam h sigma)⁻¹ 0 1 * PDE.vecDot y V +
    (gramian lam h sigma)⁻¹ 1 1 * PDE.vecDot V V

/-- Velocity component of the inverse covariance applied to the native vector pair. -/
def pform {d : ℕ} (lam h sigma : ℝ) (y V : PDE.Vec d) : PDE.Vec d :=
  (gramian lam h sigma)⁻¹ 1 0 • y + (gramian lam h sigma)⁻¹ 1 1 • V

/-- Determinant of the dimensionless covariance. -/
theorem det_ghat (lam theta : ℝ) :
    (ghat lam theta).det = lam ^ 2 *
      (1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12) := by
  rw [Matrix.det_fin_two]
  simp [ghat]
  ring

/-- Physical covariance agrees with the polynomial Gramian at every real time. -/
theorem gramian_eq_polynomial (lam : ℝ) {h : ℝ} (hh : 0 < h) (sigma : ℝ) :
    gramian lam h sigma =
      !![lam * h ^ 3 / 64 + lam * h * sigma ^ 2 / 64 + lam * sigma ^ 3 / 3,
        lam * h * sigma / 64 + lam * sigma ^ 2 / 2;
        lam * h * sigma / 64 + lam * sigma ^ 2 / 2, lam * h / 64 + lam * sigma] := by
  have hhalf : h ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) = h := by
    rw [← Real.rpow_add hh]
    norm_num
  have hthree : h ^ (3 / 2 : ℝ) = h * h ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hh, Real.rpow_one]
  have hhalf2 : (h ^ (1 / 2 : ℝ)) ^ 2 = h := by
    simpa only [pow_two] using hhalf
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [gramian, covarianceDilation, ghat, Matrix.mul_apply, Fin.sum_univ_two, hthree]
    ring_nf
    simp only [hhalf2]
  all_goals field_simp [hh.ne']
  all_goals ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
