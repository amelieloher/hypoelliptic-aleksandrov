module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing

/-!
# Shifted positive parts in reverse-time Bochner space

This module lifts the spatial shifted positive part to reverse-time `L²(V)` when
the truncation threshold depends affinely on reverse time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The totalized affine reverse-time threshold.  Its values at negative raw
times have no mathematical semantics; on nonnegative times it represents
`M + τ N`. -/
def reverseTimeAffineThreshold (M N : ℝ≥0) (τ : ℝ) : ℝ≥0 :=
  M + τ.toNNReal * N

/-- On nonnegative times, the totalized threshold has the expected real value. -/
theorem coe_reverseTimeAffineThreshold_of_nonneg
    (M N : ℝ≥0) {τ : ℝ} (hτ : 0 ≤ τ) :
    (reverseTimeAffineThreshold M N τ : ℝ) = (M : ℝ) + τ * (N : ℝ) := by
  simp only [reverseTimeAffineThreshold, NNReal.coe_add, NNReal.coe_mul,
    Real.coe_toNNReal _ hτ]

private theorem continuous_reverseTimeAffineThreshold (M N : ℝ≥0) :
    Continuous (reverseTimeAffineThreshold M N) := by
  exact continuous_const.add (continuous_real_toNNReal.mul continuous_const)

private theorem aestronglyMeasurable_reverseTimeAffineThreshold
    (T : ℝ) (M N : ℝ≥0) :
    AEStronglyMeasurable (reverseTimeAffineThreshold M N)
      (reverseTimeVolume T) :=
  (continuous_reverseTimeAffineThreshold M N).aestronglyMeasurable

private theorem aestronglyMeasurable_reverseTimeInputThresholdPair
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) : AEStronglyMeasurable
      (fun τ : ℝ => (u τ, reverseTimeAffineThreshold M N τ))
      (reverseTimeVolume T) :=
  (Lp.memLp u).aestronglyMeasurable.prodMk
    (aestronglyMeasurable_reverseTimeAffineThreshold T M N)

private theorem aestronglyMeasurable_h10ShiftedPositivePart_comp
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : α → H10HilbertGraph hΩ × ℝ≥0)
    (hp : AEStronglyMeasurable p μ) :
    AEStronglyMeasurable
      (fun x => h10ShiftedPositivePart hΩ (p x).1 (p x).2) μ := by
  exact (continuous_h10ShiftedPositivePart hΩ).comp_aestronglyMeasurable hp

private theorem aestronglyMeasurable_reverseTimeShiftedPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) : AEStronglyMeasurable
      (fun τ => h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ)) (reverseTimeVolume T) := by
  exact aestronglyMeasurable_h10ShiftedPositivePart_comp hΩ
    (fun τ : ℝ => (u τ, reverseTimeAffineThreshold M N τ))
    (aestronglyMeasurable_reverseTimeInputThresholdPair hΩ T M N u)

/-- The affine-threshold truncation belongs to the reverse-time Bochner space. -/
theorem reverseTimeShiftedPositivePart_memLp
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    MemLp (fun τ => h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume T) := by
  refine MemLp.of_le (Lp.memLp u)
    (aestronglyMeasurable_reverseTimeShiftedPositivePart hΩ T M N u) ?_
  filter_upwards with τ
  exact norm_h10ShiftedPositivePart_le hΩ (u τ)
    (reverseTimeAffineThreshold M N τ)

/-- The pointwise shifted positive part with affine threshold, lifted to
reverse-time Bochner `L²(V)`. -/
noncomputable def reverseTimeShiftedPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) : ReverseTimeL2V hΩ T :=
  (reverseTimeShiftedPositivePart_memLp hΩ T M N u).toLp
    (fun τ => h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ))

/-- The Bochner lift agrees almost everywhere with pointwise affine-threshold
truncation. -/
theorem coeFn_reverseTimeShiftedPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    reverseTimeShiftedPositivePart hΩ T M N u =ᵐ[reverseTimeVolume T]
      fun τ => h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ) :=
  (reverseTimeShiftedPositivePart_memLp hΩ T M N u).coeFn_toLp

/-- Affine-threshold shifted truncation contracts the reverse-time Bochner
norm with sharp constant one. -/
theorem norm_reverseTimeShiftedPositivePart_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    ‖reverseTimeShiftedPositivePart hΩ T M N u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hτ
  rw [hτ]
  exact norm_h10ShiftedPositivePart_le hΩ (u τ)
    (reverseTimeAffineThreshold M N τ)

/-- Pairing a reverse-time dual curve with the affine-threshold shifted
positive part is integrable. -/
theorem integrable_reverseTimeDualPairing_shiftedPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (fun τ => (g τ) (h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ))) (reverseTimeVolume T) := by
  refine (integrable_reverseTimeDualPairing hΩ T
    (reverseTimeShiftedPositivePart hΩ T M N u) g).congr ?_
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hτ
  rw [hτ]

end HypoellipticAleksandrov.Parabolic.Dirichlet
