module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedMultiplier

/-!
# Reverse-time Gelfand pairings

This module rewrites the pivot Gelfand pairing against a separated bounded
scalar multiplier as the literal spatial `L²` mass integral.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem scalarLpToH10HilbertGraphDual_apply_smul
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (u0 v0 : H10HilbertGraph hΩ) (q0 : ℝ) :
    scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ u0) (q0 • v0) =
      inner ℝ (valueCLM hΩ v0) (valueCLM hΩ u0) * q0 := by
  rw [scalarLpToH10HilbertGraphDual_apply, (valueCLM hΩ).map_smul,
    inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Pairing the Gelfand image with a bounded separated multiplier is the
literal spatial `L²` mass integral. -/
theorem reverseTimeGelfand_pairing_multiplier_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ T)
    (q : ℝ → ℝ)
    (hq : MeasureTheory.MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeGelfandCLM hΩ T u) =
      ∫ tau,
        inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * q tau
        ∂reverseTimeVolume T := by
  let G := reverseTimeGelfandCLM hΩ T u
  let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
  change reverseTimeDualPairingRightCLM hΩ T z G = _
  calc
    reverseTimeDualPairingRightCLM hΩ T z G =
        reverseTimeDualPairingCLM hΩ T G z :=
      reverseTimeDualPairingRightCLM_apply hΩ T z G
    _ = ∫ tau, G tau (z tau) ∂reverseTimeVolume T :=
      reverseTimeDualPairingCLM_apply hΩ T G z
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_reverseTimeGelfandCLM hΩ T u,
        ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hG hz
      dsimp only [G, z]
      rw [hG, hz]
      exact scalarLpToH10HilbertGraphDual_apply_smul hΩ (u tau) v (q tau)

end HypoellipticAleksandrov.Parabolic.Dirichlet
