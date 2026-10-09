module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsExtension
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Absolute continuity forced by positive smooth-test bounds

The slab convention is explicit: the tested finite measure gives no mass to the
complement of the open test region. Compact null sets are tested by their measurable
indicators; inner regularity then handles all null sets.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Smooth-test norm bounds force absolute continuity with respect to restricted Haar measure. -/
theorem absolutelyContinuous_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal) :
    μ ≪ ν.restrict U := by
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  have hcompact : ∀ K : Set E, IsCompact K → K ⊆ U → ν K = 0 → μ K = 0 := by
    intro K hK hKU hνK
    let f : E → ℝ := K.indicator (fun _ => 1)
    have hf : Measurable f := measurable_const.indicator hK.measurableSet
    have hsupport : Function.support f ⊆ K := Set.support_indicator_subset
    have hb : ∀ x, |f x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ K <;> simp [f, hx]
    have hfp := memLp_of_bounded_compact_support (ν + μ) hf hK hsupport hb p
    have hn : eLpNorm f p (ν.restrict U) = 0 := by
      have hnull : (ν.restrict U) K = 0 := by
        rw [Measure.restrict_apply hK.measurableSet]
        exact measure_mono_null inter_subset_left hνK
      rw [eLpNorm_congr_ae (show f =ᵐ[ν.restrict U] 0 from ?_)]
      · simp
      · have hx0 : ∀ᵐ x ∂ν.restrict U, x ∉ K := by
          rw [ae_iff]
          simpa only [not_not, Set.ofPred_mem_eq] using hnull
        filter_upwards [hx0] with x hx
        simp [f, hx]
    have hi := abs_integral_le_of_smooth_tests_compact ν μ hU hp hpt hC htest
      hfp hK hKU hsupport
    rw [hn, ENNReal.toReal_zero, mul_zero] at hi
    have hreal : (μ K).toReal = 0 := by
      simpa [f, integral_indicator hK.measurableSet, measureReal_def] using
        le_antisymm hi (abs_nonneg _)
    exact ((ENNReal.toReal_eq_zero_iff (μ K)).mp hreal).resolve_right
      (measure_ne_top μ K)
  intro A hA
  let A' := toMeasurable (ν.restrict U) A
  have hA' : MeasurableSet A' := measurableSet_toMeasurable _ _
  have hνA' : ν (A' ∩ U) = 0 := by
    rw [← Measure.restrict_apply hA', measure_toMeasurable]
    exact hA
  have hμA' : μ (A' ∩ U) = 0 := by
    rw [(hA'.inter hU.measurableSet).measure_eq_iSup_isCompact μ]
    apply le_antisymm _ (bot_le)
    refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
    exact (hcompact K hK (hKsub.trans inter_subset_right)
      (measure_mono_null hKsub hνA')).le
  have hμA0 : μ A' = 0 := by
    rwa [measure_inter_conull hμU] at hμA'
  exact measure_mono_null (subset_toMeasurable _ _) hμA0

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
