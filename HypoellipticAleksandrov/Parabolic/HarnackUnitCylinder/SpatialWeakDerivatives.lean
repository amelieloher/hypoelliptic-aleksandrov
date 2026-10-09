module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.DirectionalIntegrationByParts

/-! # Distributional spatial derivatives from C² time slices -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- The scalar spatial gradient supplies every first distributional spatial derivative. -/
theorem IsScalarC12On.hasWeakVelocityPartialDerivOn
    {d : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hu : IsScalarC12On u U) (i : Fin d) :
    HasWeakVelocityPartialDerivOn U i u
      (fun z => scalarSpatialGradient u z i) := by
  intro φ hφ hc hsub
  apply setIntegral_mul_directional_test hu.continuousOn
    ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient)
    (0, PDE.basisVec i) ?_ hφ hc hsub
  intro z hz
  have hs := ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  unfold HasLineDerivAt at hs ⊢
  convert hs using 1 <;> first | rfl | (funext t; congr 1; ext <;> simp)

/-- Scalar Hessian components supply second weak spatial derivatives in selected-jet order. -/
theorem IsScalarC12On.hasWeakVelocitySecondPartialDerivOn
    {d : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hu : IsScalarC12On u U) (i j : Fin d) :
    HasWeakVelocityPartialDerivOn U j
      (fun z => scalarSpatialGradient u z i)
      (fun z => scalarSpatialHessian u z i j) := by
  intro φ hφ hc hsub
  apply setIntegral_mul_directional_test
    ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient)
    ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian))
    (0, PDE.basisVec j) ?_ hφ hc hsub
  intro z hz
  have hc2 := hu.spatialSlice_contDiffAt hz
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u (z.1, y))) z.2 :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg := (hd.clm_apply (differentiableAt_const (PDE.basisVec i))).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec j)
  have heq : fderiv ℝ (fun y => (fderiv ℝ (fun w => u (z.1, w)) y) (PDE.basisVec i))
      z.2 (PDE.basisVec j) = scalarSpatialHessian u z i j := by
    rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec i)),
      scalarSpatialHessian_eq_secondFDeriv hc2]
    simpa using hc2.isSymmSndFDerivAt (by norm_num) (PDE.basisVec j) (PDE.basisVec i)
  rw [heq] at hg
  unfold HasLineDerivAt at hg ⊢
  convert hg using 1 <;> first | rfl | (funext t; simp [HasLineDerivAt,
    scalarSpatialGradient, PDE.classicalGradient, Function.comp_def])

end HypoellipticAleksandrov.Parabolic
