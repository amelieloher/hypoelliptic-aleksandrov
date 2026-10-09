module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Affine scalar calculus

This module records the pointwise scalar parabolic jets, `C¹˒²` closure,
and zero-order operator identity for a constant affine transformation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- The scalar time derivative of a constant affine transformation. -/
@[simp] theorem scalarTimeDerivative_const_mul_add_const
    {d : ℕ} (K epsilon : ℝ) (ell : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarTimeDerivative (fun q => K * ell q + epsilon) z =
      K * scalarTimeDerivative ell z := by
  unfold scalarTimeDerivative
  rw [deriv_add_const, deriv_const_mul_field]

/-- The scalar spatial gradient of a constant affine transformation. -/
@[simp] theorem scalarSpatialGradient_const_mul_add_const
    {d : ℕ} (K epsilon : ℝ) (ell : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarSpatialGradient (fun q => K * ell q + epsilon) z =
      K • scalarSpatialGradient ell z := by
  unfold scalarSpatialGradient PDE.classicalGradient
  ext i
  rw [fderiv_add_const]
  change (fderiv ℝ (K • fun y : PDE.Vec d => ell (z.1, y)) z.2) (PDE.basisVec i) = _
  rw [fderiv_const_smul_field]
  rfl

/-- The scalar spatial Hessian of a constant affine transformation. -/
@[simp] theorem scalarSpatialHessian_const_mul_add_const
    {d : ℕ} (K epsilon : ℝ) (ell : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarSpatialHessian (fun q => K * ell q + epsilon) z =
      K • scalarSpatialHessian ell z := by
  unfold scalarSpatialHessian
  have hgradient :
      (fun y : PDE.Vec d =>
          PDE.classicalGradient (fun w : PDE.Vec d => K * ell (z.1, w) + epsilon) y) =
        K • fun y : PDE.Vec d =>
          PDE.classicalGradient (fun w : PDE.Vec d => ell (z.1, w)) y := by
    funext y
    unfold PDE.classicalGradient
    ext i
    rw [fderiv_add_const]
    change (fderiv ℝ (K • fun w : PDE.Vec d => ell (z.1, w)) y) (PDE.basisVec i) = _
    rw [fderiv_const_smul_field]
    rfl
  rw [hgradient, fderiv_const_smul_field]
  rfl

/-- Scalar `C¹˒²` regularity is preserved by a constant affine transformation. -/
theorem IsScalarC12On.const_mul_add_const
    {d : ℕ} {ell : TimeVelocity d → ℝ} {Q : Set (TimeVelocity d)}
    (hell : IsScalarC12On ell Q) (K epsilon : ℝ) :
    IsScalarC12On (fun z => K * ell z + epsilon) Q := by
  refine ⟨hell.continuousOn.const_smul K |>.add continuousOn_const, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hell.timeSlice_differentiableAt hz).const_smul K |>.add_const epsilon
  · intro z hz
    exact (ContDiffAt.const_smul K (hell.spatialSlice_contDiffAt hz)).add contDiffAt_const
  · rw [show scalarTimeDerivative (fun z => K * ell z + epsilon) =
        fun z => K * scalarTimeDerivative ell z by
      funext z
      exact scalarTimeDerivative_const_mul_add_const K epsilon ell z]
    exact hell.continuousOn_scalarTimeDerivative.const_smul K
  · rw [show scalarSpatialGradient (fun z => K * ell z + epsilon) =
        fun z => K • scalarSpatialGradient ell z by
      funext z
      exact scalarSpatialGradient_const_mul_add_const K epsilon ell z]
    exact hell.continuousOn_scalarSpatialGradient.const_smul K
  · rw [show scalarSpatialHessian (fun z => K * ell z + epsilon) =
        fun z => K • scalarSpatialHessian ell z by
      funext z
      exact scalarSpatialHessian_const_mul_add_const K epsilon ell z]
    exact hell.continuousOn_scalarSpatialHessian.const_smul K

/-- The zero-order scalar parabolic operator under a constant affine transformation. -/
@[simp] theorem scalarParabolicZeroOrderOperator_const_mul_add_const
    {d : ℕ} (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (K epsilon : ℝ) (ell : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator a b c
        (fun q => K * ell q + epsilon) z =
      K * scalarParabolicZeroOrderOperator a b c ell z +
        c z.1 z.2 * epsilon := by
  have hdot (x y : PDE.Vec d) : PDE.vecDot x (K • y) = K * PDE.vecDot x y := by
    unfold PDE.vecDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [scalarParabolicZeroOrderOperator_apply,
    scalarTimeDerivative_const_mul_add_const,
    scalarSpatialGradient_const_mul_add_const,
    scalarSpatialHessian_const_mul_add_const,
    HypoellipticAleksandrov.matrixContraction_smul_right, hdot]
  ring

end HypoellipticAleksandrov.Parabolic
