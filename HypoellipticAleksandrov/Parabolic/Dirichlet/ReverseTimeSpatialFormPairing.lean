module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBochner

/-!
# Reverse-time spatial-form pairings

This module rewrites the reverse-time dual pairing of the Bochner spatial-form
action against a separated test as its literal scalar integral.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The Bochner spatial-form action paired with a separated test is its
pointwise spatial-form integral. -/
theorem reverseTimeSpatialForm_pairing_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) =
      ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau
        ∂reverseTimeVolume (r₁ - r₀) := by
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth u
  let z := reverseTimeSeparatedVTest hΩ eta v
  change reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z A = _
  have hAeval : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      ∀ w : H10HilbertGraph hΩ,
        A tau w = reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) w := by
    simpa only [A] using
      (ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u)
  calc
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z A =
        reverseTimeDualPairingCLM hΩ (r₁ - r₀) A z :=
      reverseTimeDualPairingRightCLM_apply hΩ (r₁ - r₀) z A
    _ = ∫ tau, A tau (z tau) ∂reverseTimeVolume (r₁ - r₀) :=
      reverseTimeDualPairingCLM_apply hΩ (r₁ - r₀) A z
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hAeval, ae_reverseTimeSeparatedVTest hΩ eta v] with tau hA hz
      calc
        A tau (z tau) = A tau (eta tau • v) := congrArg (A tau) hz
        _ = eta tau * A tau v := by
          rw [ContinuousLinearMap.map_smul]
          rfl
        _ = eta tau * reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v :=
          congrArg (eta tau * ·) (hA v)
        _ = reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau := mul_comm _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
