module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Borel Fourier kernels and their marginal bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- The Fourier measure of a Borel set depends measurably on the complete query. -/
theorem measurable_fourierProjection_apply {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (ξ : PDE.Vec d)
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    Measurable (fun q : EvolutionQuery Ω γ => fourierProjection K q ξ E) := by
  have hm : Measurable (fun p : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      fourierPhase ξ p.1.1.2.2.2 p.2) := by
    unfold fourierPhase PDE.vecDot
    fun_prop
  have hi := (hm.indicator (measurable_snd (hE.prod MeasurableSet.univ))).stronglyMeasurable
  have h := hi.integral_kernel_prod_right' (κ := K.master)
  convert h.measurable using 1
  funext q
  rw [fourierProjection_spec K q ξ E hE, ← integral_indicator (hE.prod MeasurableSet.univ)]
  rfl

/-- Whole-space Fourier kernels use starting position zero, removed later by covariance. -/
def fourierKernel {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) : ComplexMeasure (PDE.Vec d) :=
  fourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ

/-- The whole-space Fourier kernel satisfies the displacement integral characterization. -/
theorem fourierKernel_spec {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    IsFourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ
      (fourierKernel K σ τ hστ ξ v) :=
  fourierProjection_spec K _ ξ

/-- Whole-space Fourier kernels are Borel in their starting velocity. -/
theorem measurable_fourierKernel_apply {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec d)
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    Measurable (fun v => fourierKernel K σ τ hστ ξ v E) := by
  exact (measurable_fourierProjection_apply K ξ E hE).comp
    ((measurable_const.prodMk (measurable_const.prodMk
      (measurable_id.prodMk measurable_const))).subtype_mk)

/-- Total variation is dominated by the positive velocity marginal as a measure. -/
theorem fourierKernel_variation_le {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    (fourierKernel K σ τ hστ ξ v).variation ≤
      K.firstMarginal (wholeSpaceQuery σ τ hστ v 0) :=
  fourierProjection_variation_le K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

/-- The Fourier kernel's total variation is bounded by marginal mass. -/
theorem fourierKernel_totalVariation_le_marginal {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤
      K.firstMarginal (wholeSpaceQuery σ τ hστ v 0) univ :=
  Measure.le_iff.mp (fourierKernel_variation_le K σ τ hστ ξ v) univ MeasurableSet.univ

/-- Sub-Markov contraction bounds the Fourier kernel's total variation by one. -/
theorem fourierKernel_totalVariation_le_one {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤ 1 :=
  fourierProjection_totalVariation_le_one K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

/-- The zero mode is exactly the positive marginal embedded as a complex measure. -/
theorem fourierKernel_zero {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.Vec d) :
    fourierKernel K σ τ hστ 0 v =
      (K.firstMarginal (wholeSpaceQuery σ τ hστ v 0)).withDensityᵥ (fun _ => (1 : ℂ)) :=
  fourierProjection_zero_measure K _ _ (fourierKernel_spec K σ τ hστ 0 v)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
