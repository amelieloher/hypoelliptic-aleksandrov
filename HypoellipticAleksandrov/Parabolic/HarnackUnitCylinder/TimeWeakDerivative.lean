module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.DirectionalIntegrationByParts

/-! # Distributional time derivative from anisotropic classical regularity -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- An anisotropic C¹,² function has its scalar slice derivative as weak time derivative. -/
theorem IsScalarC12On.hasWeakTimeDerivOn
    {d : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hu : IsScalarC12On u U) :
    HasWeakTimeDerivOn U u (scalarTimeDerivative u) := by
  intro φ hφ hc hsub
  apply setIntegral_mul_directional_test hu.continuousOn
    hu.continuousOn_scalarTimeDerivative (1, 0) ?_ hφ hc hsub
  intro z hz
  unfold HasLineDerivAt
  have hs := (hu.timeSlice_hasDerivAt hz).comp_of_eq 0
    ((hasDerivAt_const 0 z.1).add (hasDerivAt_id 0)) (by simp)
  convert hs using 1
  · funext t
    congr 1
    ext <;> simp [Function.comp_def]
  · simp

end HypoellipticAleksandrov.Parabolic
