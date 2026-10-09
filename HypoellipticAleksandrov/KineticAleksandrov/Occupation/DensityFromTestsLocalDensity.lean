module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsAbsoluteContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsBounded
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Local sharp bounds for the density forced by smooth tests

The density is the real Radon–Nikodym derivative against restricted Haar measure.
The bounded-test norm argument is applied only on compact subsets, where the reference
measure is finite. Absolute continuity is proved from smooth tests in the preceding module.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The density forced by smooth tests is measurable, nonnegative, and integrable. -/
theorem rnDensity_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal) :
    let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
    Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g (ν.restrict U) ∧
      (∀ f : E → ℝ, (∫ x, f x * g x ∂ν.restrict U) = ∫ x, f x ∂μ) ∧
      (∫ x, g x ∂ν.restrict U) = (μ univ).toReal := by
  have hac := absolutelyContinuous_of_smooth_tests ν μ hU hμU hp hpt hC htest
  dsimp only
  refine ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · have hi := Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := ν.restrict U)
      (measure_ne_top μ univ)
    simpa only [integrableOn_univ] using hi
  · intro f
    simpa only [mul_comm] using integral_toReal_rnDeriv_mul hac (f := f)
  · simpa only [measureReal_def] using Measure.integral_toReal_rnDeriv hac

/-- The Radon–Nikodym density has the sharp `Lʳ` bound on each compact interior subset. -/
theorem rnDensity_compact_norm_le (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C *
        (eLpNorm f (ENNReal.ofReal (r / (r - 1))) (ν.restrict U)).toReal)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
    MemLp g (ENNReal.ofReal r) ((ν.restrict U).restrict K) ∧
      (eLpNorm g (ENNReal.ofReal r) ((ν.restrict U).restrict K)).toReal ≤ C := by
  let p := ENNReal.ofReal (r / (r - 1))
  have hp : 1 ≤ p := by
    apply ENNReal.one_le_ofReal.mpr
    exact (le_div_iff₀ (by linarith)).2 (by linarith)
  have hpt : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hac := absolutelyContinuous_of_smooth_tests ν μ hU hμU hp hpt hC htest
  have hprops := rnDensity_of_smooth_tests ν μ hU hμU hp hpt hC htest
  let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
  have hfin : IsFiniteMeasure ((ν.restrict U).restrict K) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.restrict_eq_self ν hKU]
    exact hK.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  apply memLp_and_eLpNorm_le_of_bounded_conjugate_tests hr hC hprops.1
    hprops.2.2.1.restrict
  intro φ hφ hφbound
  obtain ⟨M, hM, hφM⟩ := hφbound
  let f := K.indicator φ
  have hf : Measurable f := hφ.indicator hK.measurableSet
  have hfK : Function.support f ⊆ K := Set.support_indicator_subset
  have hfM : ∀ x, |f x| ≤ M := by
    intro x
    by_cases hx : x ∈ K
    · simpa [f, hx] using hφM x
    · simpa [f, hx] using hM
  have hfp := memLp_of_bounded_compact_support (ν + μ) hf hK hfK hfM p
  have hb := abs_integral_le_of_smooth_tests_compact ν μ hU hp hpt hC htest
    hfp hK hKU hfK
  have hpair : (∫ x, φ x * g x ∂(ν.restrict U).restrict K) = ∫ x, f x ∂μ := by
    rw [show (fun x => φ x * g x) = (fun x => g x * φ x) by
      funext x; exact mul_comm _ _]
    change (∫ x in K, (μ.rnDeriv (ν.restrict U) x).toReal * φ x ∂ν.restrict U) = _
    rw [setIntegral_toReal_rnDeriv_mul hac hK.measurableSet,
      ← integral_indicator hK.measurableSet]
  rw [hpair]
  simpa only [f, eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
