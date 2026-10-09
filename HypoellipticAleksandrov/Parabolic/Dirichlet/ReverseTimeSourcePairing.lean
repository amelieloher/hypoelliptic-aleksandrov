module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner

/-!
# Reverse-time source pairings

This module rewrites the dual pairing of the already-negative reverse-time
source against a separated test as its literal raw-source integral.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Pairing the negative reverse-time source with a separated test equals its
literal raw-source integral. -/
theorem reverseTimeNegativeSource_pairing_eq_integral_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) =
      ∫ tau,
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v *
          eta tau
        ∂reverseTimeVolume (r₁ - r₀) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let z := reverseTimeSeparatedVTest hΩ eta v
  change reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z S = _
  have hSeval : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      S tau = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau := by
    exact
      (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp
  calc
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z S =
        reverseTimeDualPairingCLM hΩ (r₁ - r₀) S z :=
      reverseTimeDualPairingRightCLM_apply hΩ (r₁ - r₀) z S
    _ = ∫ tau, S tau (z tau) ∂reverseTimeVolume (r₁ - r₀) :=
      reverseTimeDualPairingCLM_apply hΩ (r₁ - r₀) S z
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hSeval, ae_reverseTimeSeparatedVTest hΩ eta v] with tau hS hz
      calc
        S tau (z tau) = S tau (eta tau • v) := congrArg (S tau) hz
        _ = eta tau * S tau v := by
          rw [ContinuousLinearMap.map_smul]
          rfl
        _ = eta tau *
            reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v :=
          congrArg (fun g => eta tau * g v) hS
        _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v *
            eta tau := mul_comm _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
