module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing

/-!
# Positive parts in reverse-time Bochner space

This module lifts the spatial `H¹₀` positive-part operation pointwise to the
reverse-time Bochner `L²` space.  The lift is valid for every real terminal time,
including the empty-interval case, and retains the sharp constant-one norm
contraction.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The pointwise positive part remains in reverse-time Bochner L². -/
theorem reverseTimePositivePart_memLp
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
    MemLp (fun τ => h10PositivePart hΩ (u τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume T) := by
  apply MemLp.of_le (Lp.memLp u)
  · exact continuous_h10PositivePart hΩ |>.comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  · filter_upwards with τ
    exact norm_h10PositivePart_le hΩ (u τ)

/-- The pointwise spatial positive part, canonically lifted to reverse-time
Bochner `L²(V)`. -/
noncomputable def reverseTimePositivePart
    (hΩ : IsOpen Ω) (T : ℝ) : ReverseTimeL2V hΩ T → ReverseTimeL2V hΩ T :=
  fun u => (reverseTimePositivePart_memLp hΩ T u).toLp
    (fun τ => h10PositivePart hΩ (u τ))

/-- The reverse-time Bochner positive part agrees almost everywhere with the
pointwise spatial `H¹₀` positive part. -/
theorem coeFn_reverseTimePositivePart
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
    reverseTimePositivePart hΩ T u =ᵐ[reverseTimeVolume T]
      fun τ => h10PositivePart hΩ (u τ) :=
  (reverseTimePositivePart_memLp hΩ T u).coeFn_toLp

/-- Taking the reverse-time Bochner positive part contracts the `L²(V)` norm
with sharp constant one. -/
theorem norm_reverseTimePositivePart_le
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
    ‖reverseTimePositivePart hΩ T u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with τ hτ
  rw [hτ]
  exact norm_h10PositivePart_le hΩ (u τ)

/-- Pairing a reverse-time `L²(V*)` curve with the pointwise positive part of
a reverse-time `L²(V)` curve is integrable. -/
theorem integrable_reverseTimeDualPairing_positivePart
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (fun τ => (g τ) (h10PositivePart hΩ (u τ)))
      (reverseTimeVolume T) := by
  refine (integrable_reverseTimeDualPairing hΩ T
    (reverseTimePositivePart hΩ T u) g).congr ?_
  filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with τ hτ
  rw [hτ]

end HypoellipticAleksandrov.Parabolic.Dirichlet
