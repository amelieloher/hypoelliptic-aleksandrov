module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of reverse-time dual pairings

This module proves the `L¹` integrability of the pointwise pairing of the
reverse-time `L²(V*)` and `L²(V)` Bochner representatives.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The literal pointwise dual pairing of reverse-time `L²(V*)` and `L²(V)`
curves is integrable on the reverse-time volume. -/
theorem integrable_reverseTimeDualPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    MeasureTheory.Integrable (fun tau => (g tau) (u tau))
      (reverseTimeVolume T) := by
  let pairing : H10HilbertGraphDual hΩ →L[ℝ]
      H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  have hpair : MeasureTheory.MemLp
      (fun tau => pairing (g tau) (u tau)) (1 : ℝ≥0∞)
      (reverseTimeVolume T) :=
    pairing.memLp_of_bilin 1 (MeasureTheory.Lp.memLp g)
      (MeasureTheory.Lp.memLp u)
  simpa only [pairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply] using memLp_one_iff_integrable.mp hpair

end HypoellipticAleksandrov.Parabolic.Dirichlet
