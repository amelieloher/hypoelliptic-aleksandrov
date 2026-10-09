module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic

/-! # Velocity jets of the constructed Gaussian profile at positive block times -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic

/-- For fixed covariance time the native velocity quadratic is smooth everywhere. -/
theorem contDiff_qform_velocity {d : ℕ} (lam h sigma : ℝ) (y : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun V => qform lam h sigma y V) := by
  unfold qform PDE.vecDot
  fun_prop

/-- The profile velocity slice factors into an exponential quadratic and a constant. -/
theorem gaussianProfile_velocitySlice {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y : PDE.Vec d) :
    (fun V => gaussianProfile lam Lam H h L ell sblock (s, (y, V))) =
      (fun V => (ell * Real.exp (-Xi d lam Lam H h * (s - sblock))) *
        Real.exp (-qform lam h (s - sblock) y V) + (-ell * Real.exp (-L ^ 2))) := by
  funext V
  rw [gaussianProfile_of_pos lam Lam H L ell sblock hh hs]
  rw [sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ring

/-- The profile velocity gradient is exactly minus twice amplitude times Gaussian times `p`. -/
theorem gaussianProfile_velocityGradient {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    PDE.classicalGradient
      (fun W => gaussianProfile lam Lam H h L ell sblock (s, (y, W))) V =
      (-2 * ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V)) • pform lam h (s - sblock) y V := by
  have hq := (contDiff_qform_velocity lam h (s - sblock) y).differentiable (by norm_num) V
  have hExp : DifferentiableAt ℝ (fun W => Real.exp (-qform lam h (s - sblock) y W)) V :=
    hq.neg.exp
  have hMul : DifferentiableAt ℝ (fun W =>
      (ell * Real.exp (-Xi d lam Lam H h * (s - sblock))) *
        Real.exp (-qform lam h (s - sblock) y W)) V :=
    (differentiableAt_const _).mul hExp
  rw [gaussianProfile_velocitySlice lam Lam H L ell sblock hh hs,
    classicalGradient_add hMul (differentiableAt_const _),
    classicalGradient_const_mul _ hExp,
    classicalGradient_exp_neg hq]
  have hzero : PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) V = 0 := by
    ext i
    simp [PDE.classicalGradient]
  rw [hzero, add_zero]
  have hgrad := kineticVelocityGradient_qform lam hh (s - sblock) y V
  change PDE.classicalGradient (fun W => qform lam h (s - sblock) y W) V = _ at hgrad
  rw [hgrad, sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The profile velocity Hessian has the exact Gaussian rank-one minus covariance form. -/
theorem gaussianProfile_velocityHessian {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun W => gaussianProfile lam Lam H h L ell sblock (s, (y, W))) V i j =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
      (4 * pform lam h (s - sblock) y V i * pform lam h (s - sblock) y V j -
        2 * (gramian lam h (s - sblock))⁻¹ 1 1 * (1 : PDE.Mat d) i j) := by
  have hq : ContDiff ℝ 2 (fun W => qform lam h (s - sblock) y W) :=
    (contDiff_qform_velocity lam h (s - sblock) y).of_le (by norm_cast)
  rw [gaussianProfile_velocitySlice lam Lam H L ell sblock hh hs,
    sliceHessian_add (contDiffAt_const.mul hq.contDiffAt.neg.exp) contDiffAt_const,
    sliceHessian_const_mul _ hq.contDiffAt.neg.exp]
  have hz : sliceHessian (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) V = 0 := by
    have hc : (fun W : PDE.Vec d =>
        PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W) =
        (fun _ => (0 : PDE.Vec d)) := by
      funext W
      ext k
      change (fderiv ℝ (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W)
        (PDE.basisVec k) = 0
      rw [fderiv_const_apply]
      rfl
    ext k l
    change (fderiv ℝ (fun W : PDE.Vec d =>
        PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W) V)
        (PDE.basisVec k) l = 0
    rw [hc, fderiv_const_apply]
    rfl
  rw [hz, add_zero, Matrix.smul_apply, sliceHessian_exp_neg hq]
  have hgrad := kineticVelocityGradient_qform lam hh (s - sblock) y V
  change PDE.classicalGradient (fun W => qform lam h (s - sblock) y W) V = _ at hgrad
  have hhess := kineticVelocityHessian_qform lam (h := h) (s - sblock) y V
  rw [kineticVelocityHessian_eq_sliceHessian] at hhess
  rw [hgrad, hhess]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rw [sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
