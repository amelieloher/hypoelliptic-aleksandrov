module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.Replacement
public import HypoellipticAleksandrov.Parabolic.TimeReversal
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Time reflection of anisotropic classical replacements

The existing reflection t ↦ 1-t preserves the C12 carrier and changes the sign of
the time derivative. No second time derivative is required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Time reflection reverses the scalar time derivative for the anisotropic carrier. -/
theorem scalarTimeDerivative_timeReflectedScalar_C12 {d : ℕ}
    {u : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)} (hu : IsScalarC12On u D)
    {z : TimeVelocity d} (hz : timeReflection z ∈ D) :
    scalarTimeDerivative (timeReflectedScalar u) z =
      -scalarTimeDerivative u (timeReflection z) := by
  have h := (hu.timeSlice_hasDerivAt hz).comp z.1
    ((hasDerivAt_const z.1 (1 : ℝ)).sub (hasDerivAt_id z.1))
  change deriv (fun t => u (1 - t, z.2)) z.1 = _
  simpa only [Function.comp_def, timeReflection, Pi.sub_apply, id_eq, zero_sub,
    mul_neg, mul_one] using h.deriv

/-- Spatial gradients are unaffected by reflecting only time. -/
theorem scalarSpatialGradient_timeReflectedScalar_C12 {d : ℕ}
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarSpatialGradient (timeReflectedScalar u) z =
      scalarSpatialGradient u (timeReflection z) := rfl

/-- Spatial Hessians are unaffected by reflecting only time. -/
theorem scalarSpatialHessian_timeReflectedScalar_C12 {d : ℕ}
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    scalarSpatialHessian (timeReflectedScalar u) z =
      scalarSpatialHessian u (timeReflection z) := rfl

/-- The anisotropic classical carrier transports through the existing time reflection. -/
theorem isScalarC12On_timeReflectedScalar {d : ℕ} {u : TimeVelocity d → ℝ}
    {D : Set (TimeVelocity d)} (hu : IsScalarC12On u D) :
    IsScalarC12On (timeReflectedScalar u) (timeReflection ⁻¹' D) := by
  have hmaps : MapsTo timeReflection (timeReflection ⁻¹' D) D := fun _ hz => hz
  refine ⟨hu.continuousOn.comp continuous_timeReflection.continuousOn hmaps, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro z hz
    have h := (hu.timeSlice_hasDerivAt hz).comp z.1
      ((hasDerivAt_const z.1 (1 : ℝ)).sub (hasDerivAt_id z.1))
    exact h.differentiableAt
  · intro z hz
    exact hu.spatialSlice_contDiffAt hz
  · apply (hu.continuousOn_scalarTimeDerivative.comp
      continuous_timeReflection.continuousOn hmaps).neg.congr
    intro z hz
    exact scalarTimeDerivative_timeReflectedScalar_C12 hu hz
  · exact hu.continuousOn_scalarSpatialGradient.comp
      continuous_timeReflection.continuousOn hmaps
  · exact hu.continuousOn_scalarSpatialHessian.comp
      continuous_timeReflection.continuousOn hmaps

/-- A backward homogeneous classical equation becomes the forward homogeneous equation. -/
theorem homogeneous_timeReflectedScalar_C12 {d : ℕ} (A : CoefficientField d)
    {u : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)} (hu : IsScalarC12On u D)
    (heq : ∀ z ∈ D, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    ∀ z ∈ timeReflection ⁻¹' D,
      scalarTimeDerivative (timeReflectedScalar u) z =
        matrixContraction (coefficientAt (timeReflectedCoefficient A) z)
          (scalarSpatialHessian (timeReflectedScalar u) z) := by
  intro z hz
  rw [scalarTimeDerivative_timeReflectedScalar_C12 hu hz,
    scalarSpatialHessian_timeReflectedScalar_C12, coefficientAt_timeReflectedCoefficient]
  linarith only [heq (timeReflection z) hz]

end HypoellipticAleksandrov.Parabolic.LocalHolder
