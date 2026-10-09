module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeShiftedPositivePart
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Spatial mass on bounded domains

This module packages integration over a bounded spatial domain as a continuous
linear functional on `L²`.  It also proves time integrability of that functional
applied to the affine-threshold shifted positive part.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Integration over a bounded spatial domain, as a continuous linear
functional on its restricted-volume `L²` space. -/
noncomputable def spatialMassCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩbounded : Bornology.IsBounded Ω) :
    MeasureTheory.Lp ℝ 2 (PDE.volumeOn Ω) →L[ℝ] ℝ := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  let pairing : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  exact ContinuousLinearMap.flip
    (pairing.lpPairing (PDE.volumeOn Ω) (2 : ℝ≥0∞) (2 : ℝ≥0∞))
    (MeasureTheory.Lp.const (2 : ℝ≥0∞) (PDE.volumeOn Ω) 1)

/-- Spatial mass is the literal integral of the chosen `L²` representative. -/
theorem spatialMassCLM_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩbounded : Bornology.IsBounded Ω)
    (f : MeasureTheory.Lp ℝ 2 (PDE.volumeOn Ω)) :
    spatialMassCLM hΩbounded f = ∫ y, f y ∂PDE.volumeOn Ω := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  unfold spatialMassCLM
  dsimp only
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing (PDE.volumeOn Ω)
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) f
        (MeasureTheory.Lp.const (2 : ℝ≥0∞) (PDE.volumeOn Ω) 1) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.Lp.coeFn_const (p := (2 : ℝ≥0∞))
    (μ := PDE.volumeOn Ω) (1 : ℝ)] with y hy
  calc
    (f y) * (MeasureTheory.Lp.const (2 : ℝ≥0∞)
        (PDE.volumeOn Ω) (1 : ℝ) y) = (f y) * 1 := congrArg (fun z : ℝ => (f y) * z) hy
    _ = f y := mul_one _

/-- The spatial mass of the affine-threshold shifted positive part is
integrable in reverse time. -/
theorem integrable_reverseTimeShiftedPositivePart_spatialMass
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (T : ℝ) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) :
    Integrable (fun τ => ∫ y,
      valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ)) y ∂PDE.volumeOn Ω)
      (reverseTimeVolume T) := by
  let Q : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  let w : ReverseTimeL2V hΩ T := reverseTimeShiftedPositivePart hΩ T M N u
  let Qw : MeasureTheory.Lp ℝ 2 (reverseTimeVolume T) :=
    Q.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) w
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    infer_instance
  have hQw : Qw =ᵐ[reverseTimeVolume T] fun τ =>
      spatialMassCLM hΩbounded
        (valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ)
          (reverseTimeAffineThreshold M N τ))) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL Q w,
      coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hQ hshift
    dsimp only [Qw]
    rw [hQ]
    dsimp only [Q, w, ContinuousLinearMap.comp_apply]
    rw [hshift]
  refine ((MeasureTheory.Lp.memLp Qw).integrable (by norm_num)).congr ?_
  filter_upwards [hQw] with τ hτ
  rw [hτ, spatialMassCLM_apply]

end HypoellipticAleksandrov.Parabolic.Dirichlet
