module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelNormLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Exhaustion of the source norm without a sign assumption on the estimate constant -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter Set
open scoped Topology

/-- Eventual a.e. coverage exhausts the nonnegative finite source norm. -/
theorem borel_indicator_norm_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 0 < p) (F : E → ℝ) (hF : MemLp F (ENNReal.ofReal p) μ)
    (hnn : ∀ᵐ z ∂μ, 0 ≤ F z) (S : ℕ → Set E) (hS : ∀ j, MeasurableSet (S j))
    (hcover : ∀ᵐ z ∂μ, ∀ᶠ j in atTop, z ∈ S j) :
    Tendsto (fun j => (eLpNorm ((S j).indicator F) (ENNReal.ofReal p) μ).toReal)
      atTop (𝓝 (eLpNorm F (ENNReal.ofReal p) μ).toReal) := by
  let G := fun j => (S j).indicator F
  have hG j : MemLp (G j) (ENNReal.ofReal p) μ := hF.indicator (hS j)
  have hGn j : ∀ᵐ z ∂μ, 0 ≤ G j z := by
    filter_upwards [hnn] with z hz
    by_cases hs : z ∈ S j
    · simpa only [G,indicator_of_mem hs] using hz
    · simp only [G,indicator_of_notMem hs,le_refl]
  have hmeas j : AEStronglyMeasurable (fun z => ‖G j z‖ ^ p) μ :=
    (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable (hG j).aestronglyMeasurable.norm
  have hi : Integrable (fun z => ‖F z‖ ^ p) μ := by
    have ht := hF.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using ht
  have hb j : ∀ᵐ z ∂μ, ‖‖G j z‖ ^ p‖ ≤ ‖F z‖ ^ p := by
    filter_upwards with z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    by_cases hs : z ∈ S j
    · simp only [G,indicator_of_mem hs,le_refl]
    · simp only [G,indicator_of_notMem hs,norm_zero,norm_nonneg]
  have hc : ∀ᵐ z ∂μ, Tendsto (fun j => ‖G j z‖ ^ p) atTop (𝓝 (‖F z‖ ^ p)) := by
    filter_upwards [hcover] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with j hj
    simp only [G,indicator_of_mem hj]
  have ht := tendsto_integral_of_dominated_convergence (fun z => ‖F z‖ ^ p)
    hmeas hi hb hc
  have hroot := (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).continuousAt.tendsto.comp
    ht
  have heq j : (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal =
      (∫ z, ‖G j z‖ ^ p ∂μ) ^ (1 / p) := by
    rw [abp_eLpNorm_toReal_nonneg hp (hG j) (hGn j)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hGn j] with z hz
    rw [Real.norm_of_nonneg hz]
  have heqF : (eLpNorm F (ENNReal.ofReal p) μ).toReal =
      (∫ z, ‖F z‖ ^ p ∂μ) ^ (1 / p) := by
    rw [abp_eLpNorm_toReal_nonneg hp hF hnn]
    congr 1
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    rw [Real.norm_of_nonneg hz]
  simpa only [Function.comp_def,← heq,← heqF,G] using hroot

end HypoellipticAleksandrov.KineticAleksandrov
