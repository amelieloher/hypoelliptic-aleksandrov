module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedTest

/-!
# Right reverse-time dual pairings

This module normalizes evaluation of the reverse-time dual pairing at a fixed
primal `L²(V)` test.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time dual pairing evaluated at a fixed primal test on the right. -/
noncomputable def reverseTimeDualPairingRightCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (z : ReverseTimeL2V hΩ T) : ReverseTimeL2VStar hΩ T →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ z).comp (reverseTimeDualPairingCLM hΩ T)

/-- Right evaluation of `reverseTimeDualPairingRightCLM`. -/
@[simp] theorem reverseTimeDualPairingRightCLM_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (z : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    reverseTimeDualPairingRightCLM hΩ T z g =
      reverseTimeDualPairingCLM hΩ T g z := rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
