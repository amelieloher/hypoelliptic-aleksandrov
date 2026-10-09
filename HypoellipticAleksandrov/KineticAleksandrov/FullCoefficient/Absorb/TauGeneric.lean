module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Differentiation under the integral over a finite measure space

A form of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a constant dominating bound on
a closed ball in the parameter, used for the integration in the slice time `τ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem hasDerivAt_integral_const_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F F' : ℝ → α → ℝ} {h b : ℝ} (hh : 0 < h)
    (hmeas : ∀ s ∈ Metric.closedBall h (h / 2), AEStronglyMeasurable (F s) μ)
    (hint : Integrable (F h) μ) (hmeas' : AEStronglyMeasurable (F' h) μ)
    (hdiff : ∀ᵐ a ∂μ, ∀ s ∈ Metric.closedBall h (h / 2), HasDerivAt (fun s => F s a) (F' s a) s)
    (hbd : ∀ᵐ a ∂μ, ∀ s ∈ Metric.closedBall h (h / 2), |F' s a| ≤ b) :
    Integrable (F' h) μ ∧ HasDerivAt (fun s => ∫ a, F s a ∂μ) (∫ a, F' h a ∂μ) h := by
  have hε : 0 < h / 2 := by positivity
  have hnhds : Metric.closedBall h (h / 2) ∈ nhds h := Metric.closedBall_mem_nhds h hε
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => b) hnhds
    (Filter.eventually_of_mem hnhds hmeas) hint hmeas' ?_ (integrable_const b) hdiff
  filter_upwards [hbd] with a ha s hs
  rw [Real.norm_eq_abs]
  exact ha s hs

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
