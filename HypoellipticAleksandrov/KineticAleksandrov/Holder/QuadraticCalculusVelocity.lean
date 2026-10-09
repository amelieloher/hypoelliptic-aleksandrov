module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculus
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Velocity gradient and Hessian of the kinetic covariance quadratic form -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open HypoellipticAleksandrov.Parabolic
open scoped BigOperators

/-- Explicit classical gradient of a scalar Euclidean quadratic with a linear term. -/
theorem classicalGradient_velocity_quadratic {d : ℕ} (C b c : ℝ) (y W : PDE.Vec d) :
    PDE.classicalGradient (fun V => C + 2 * b * PDE.vecDot y V + c * PDE.vecDot V V) W =
      (2 * b) • y + (2 * c) • W := by
  have hl := HasFDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin d) _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) i W).const_mul (y i))
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin d) _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) i W).pow 2)
  have hp := ((hasFDerivAt_const C W).add (hl.const_mul (2 * b))).add (hq.const_mul c)
  have heq : (fun V => C + 2 * b * PDE.vecDot y V + c * PDE.vecDot V V) =
      (fun V => C + 2 * b * (∑ i, y i * V i) + c * (∑ i, (V i) ^ 2)) := by
    funext V
    unfold PDE.vecDot
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  ext i
  unfold PDE.classicalGradient
  change HasFDerivAt (fun V : PDE.Vec d =>
    C + 2 * b * (∑ j, y j * V j) + c * (∑ j, (V j) ^ 2)) _ W at hp
  rw [hp.fderiv]
  simp [PDE.basisVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The velocity gradient is twice the velocity component of inverse covariance. -/
theorem kineticVelocityGradient_qform {d : ℕ} (lam : ℝ) {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (y V : PDE.Vec d) :
    kineticVelocityGradient
      (fun P : KineticPoint d => qform lam h sigma P.position P.velocity) ⟨0, y, V⟩ =
      2 • pform lam h sigma y V := by
  have heq : (fun W => qform lam h sigma y W) =
      (fun W => (gramian lam h sigma)⁻¹ 0 0 * PDE.vecDot y y +
        2 * (gramian lam h sigma)⁻¹ 0 1 * PDE.vecDot y W +
        (gramian lam h sigma)⁻¹ 1 1 * PDE.vecDot W W) := rfl
  change PDE.classicalGradient (fun W => qform lam h sigma y W) V = _
  rw [heq, classicalGradient_velocity_quadratic]
  unfold pform
  rw [gramian_inv_blocks lam hh]
  ext i
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- The velocity Hessian is twice the velocity block of inverse covariance. -/
theorem kineticVelocityHessian_qform {d : ℕ} (lam : ℝ) {h : ℝ}
    (sigma : ℝ) (y V : PDE.Vec d) :
    kineticVelocityHessian
      (fun P : KineticPoint d => qform lam h sigma P.position P.velocity) ⟨0, y, V⟩ =
      (2 * (gramian lam h sigma)⁻¹ 1 1) • (1 : PDE.Mat d) := by
  have hg : (fun W => PDE.classicalGradient (fun U => qform lam h sigma y U) W) =
      (fun W => (2 * (gramian lam h sigma)⁻¹ 0 1) • y +
        (2 * (gramian lam h sigma)⁻¹ 1 1) • W) := by
    funext W
    exact classicalGradient_velocity_quadratic
      ((gramian lam h sigma)⁻¹ 0 0 * PDE.vecDot y y)
      ((gramian lam h sigma)⁻¹ 0 1) ((gramian lam h sigma)⁻¹ 1 1) y W
  unfold kineticVelocityHessian
  change (fun i j => (fderiv ℝ
    (fun W => PDE.classicalGradient (fun U => qform lam h sigma y U) W) V)
    (PDE.basisVec i) j) = _
  rw [hg]
  have hp := (hasFDerivAt_id (𝕜 := ℝ) V).const_smul
    (2 * (gramian lam h sigma)⁻¹ 1 1)
  have hd := hp.const_add ((2 * (gramian lam h sigma)⁻¹ 0 1) • y)
  have hder : fderiv ℝ (fun W => (2 * (gramian lam h sigma)⁻¹ 0 1) • y +
      (2 * (gramian lam h sigma)⁻¹ 1 1) • W) V =
      (2 * (gramian lam h sigma)⁻¹ 1 1) • ContinuousLinearMap.id ℝ (PDE.Vec d) := by
    simpa only [Pi.smul_apply, id_eq] using hd.fderiv
  rw [hder]
  ext i j
  simp [PDE.basisVec_apply, Matrix.one_apply, Matrix.smul_apply, eq_comm]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
