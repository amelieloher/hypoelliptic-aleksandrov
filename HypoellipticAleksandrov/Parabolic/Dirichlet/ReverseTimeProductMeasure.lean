module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Reverse-time product measure

This module identifies the literal reverse-time restricted product volume with
the restricted time--velocity volume on a product set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory

/-- The literal reverse-time and velocity restricted volumes form the
time--velocity restricted volume on their product set. -/
theorem reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn
    {d : ℕ} (T : ℝ) (Ω : Set (PDE.Vec d)) :
    (reverseTimeVolume T).prod (PDE.volumeOn Ω) =
      timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω) := by
  rw [reverseTimeVolume, timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
  simpa using Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (PDE.Vec d))) (reverseTimeOpenInterval T) Ω

end HypoellipticAleksandrov.Parabolic.Dirichlet
