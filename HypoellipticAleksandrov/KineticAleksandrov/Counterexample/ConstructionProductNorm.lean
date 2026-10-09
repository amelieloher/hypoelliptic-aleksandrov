module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Exact time factors for stationary source norms -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped ENNReal

/-- A stationary spatial field acquires precisely the finite time-measure factor. -/
theorem construction_eLpNorm_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [SFinite nu] (f : Y → ℝ) (hf : Measurable f)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun q : X × Y => f q.2) p (mu.prod nu) =
      (mu Set.univ) ^ (1 / p.toReal) * eLpNorm f p nu := by
  have hm : Measurable (fun q : X × Y => f q.2) := hf.comp measurable_snd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable]
  rw [lintegral_prod _ (hm.enorm.pow_const p.toReal).aemeasurable]
  simp only [lintegral_const]
  rw [ENNReal.mul_rpow_of_nonneg]
  · rw [mul_comm]
  · exact (one_div_pos.mpr (ENNReal.toReal_pos hp0 hpTop)).le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
