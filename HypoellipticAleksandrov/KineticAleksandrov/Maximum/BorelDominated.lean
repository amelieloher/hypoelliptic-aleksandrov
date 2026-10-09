module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Dominated convergence for the fixed-inner-cylinder error -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter
open scoped Topology

/-- Bounded nonnegative errors converging a.e. vanish in every finite real Lp norm. -/
theorem borel_bounded_error_norm_tendsto {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (e : ℕ → E → ℝ) (hm : ∀ j, AEStronglyMeasurable (e j) μ)
    (hnn : ∀ j, ∀ᵐ z ∂μ, 0 ≤ e j z)
    (hb : ∀ j, ∀ᵐ z ∂μ, e j z ≤ B)
    (hc : ∀ᵐ z ∂μ, Tendsto (fun j => e j z) atTop (𝓝 0)) :
    Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0) := by
  have hmem j : MemLp (e j) (ENNReal.ofReal p) μ := by
    apply (memLp_const B).of_le (hm j)
    filter_upwards [hnn j,hb j] with z hz hzB
    simpa only [Real.norm_of_nonneg hz,Real.norm_of_nonneg hB] using hzB
  have hpower j : AEStronglyMeasurable (fun z => e j z ^ p) μ :=
    (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable (hm j)
  have hbound j : ∀ᵐ z ∂μ, ‖e j z ^ p‖ ≤ B ^ p := by
    filter_upwards [hnn j,hb j] with z hz hzB
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hz _)]
    exact Real.rpow_le_rpow hz hzB hp.le
  have hconv : ∀ᵐ z ∂μ, Tendsto (fun j => e j z ^ p) atTop (𝓝 0) := by
    filter_upwards [hc] with z hz
    simpa only [Function.comp_def,Real.zero_rpow hp.ne'] using
      (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp hz
  have hi := tendsto_integral_of_dominated_convergence (fun _ : E => B ^ p)
    hpower (integrable_const _) hbound hconv
  simp only [integral_zero] at hi
  have hr := (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).tendsto 0
  have ht := hr.comp hi
  simp only [Function.comp_def,Real.zero_rpow (by positivity : 1 / p ≠ 0)] at ht
  convert ht using 1
  funext j
  exact abp_eLpNorm_toReal_nonneg hp (hmem j) (hnn j)

end HypoellipticAleksandrov.KineticAleksandrov
