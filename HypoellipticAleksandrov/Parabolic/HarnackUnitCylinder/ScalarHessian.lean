module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Symmetry of the scalar spatial Hessian -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- The scalar Hessian equals the second derivative of the fixed-time slice. -/
theorem scalarSpatialHessian_eq_secondFDeriv
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 (fun y => u (z.1, y)) z.2) (i j : Fin d) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y => u (z.1, y))) z.2 (PDE.basisVec i)
        (PDE.basisVec j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u (z.1, y))) z.2 :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold scalarSpatialHessian PDE.classicalGradient
  rw [fderiv_pi (fun k => hd.clm_apply (differentiableAt_const (PDE.basisVec k)))]
  simp only [ContinuousLinearMap.pi_apply]
  rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
  simp

/-- Spatial C² slices give the exact scalar Hessian symmetry, without time regularity. -/
theorem scalarSpatialHessian_isSymm_of_c12
    {d : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hu : IsScalarC12On u U) {z : TimeVelocity d} (hz : z ∈ U) :
    (scalarSpatialHessian u z).IsSymm := by
  have hs := hu.spatialSlice_contDiffAt hz
  ext i j
  change scalarSpatialHessian u z j i = scalarSpatialHessian u z i j
  rw [scalarSpatialHessian_eq_secondFDeriv hs, scalarSpatialHessian_eq_secondFDeriv hs]
  exact hs.isSymmSndFDerivAt (by norm_num) _ _

end HypoellipticAleksandrov.Parabolic
