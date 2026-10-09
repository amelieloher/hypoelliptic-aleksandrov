module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBoundedFormEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalTimewiseOperator

/-!
# Weighted reverse-time variational energy identity

This module composes the bounded pivot-factorization energy identity with the
timewise reverse-time variational residual evaluation.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A reverse-time variational energy solution satisfies the bounded-pivot
weighted energy identity with its source-minus-form residual. -/
theorem
    IsReverseTimeVariationalEnergySolution.integral_value_norm_sq_mul_reverseTimeScalarTest_deriv_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hfactor : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y)))
    (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    (∫ t,
      ‖valueCLM hΩ (A (u t))‖ ^ 2 * eta.deriv t
        ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ t,
        (2 *
          ((reverseTimeNegativeSource
              r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth t) (S (u t)) -
            (reverseTimeSpatialFormBochnerAction
              r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth u t) (S (u t)))) * eta t
          ∂reverseTimeVolume (r₁ - r₀)) := by
  calc
    (∫ t,
      ‖valueCLM hΩ (A (u t))‖ ^ 2 * eta.deriv t
        ∂reverseTimeVolume (r₁ - r₀)) =
        -(∫ t, (2 * (g t) (S (u t))) * eta t
          ∂reverseTimeVolume (r₁ - r₀)) := by
      exact
      integral_value_norm_sq_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_pivot_factorization
        hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) A S hfactor u g hdu eta
    _ = -(∫ t,
        (2 *
          ((reverseTimeNegativeSource
              r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth t) (S (u t)) -
            (reverseTimeSpatialFormBochnerAction
              r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth u t) (S (u t)))) * eta t
          ∂reverseTimeVolume (r₁ - r₀)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards
        [ae_reverseTimeVariationalEnergySolution_apply_timewiseCLM
          r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
          initial u g hdu hu S] with t ht
      rw [ht]

end HypoellipticAleksandrov.Parabolic.Dirichlet
