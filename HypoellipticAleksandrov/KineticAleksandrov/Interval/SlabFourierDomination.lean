module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierBound

/-! # Evolved variation domination and the killed half-time bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal ProbabilityTheory

/-- Phase-weighted evolution has variation dominated by the positive pushed marginal. -/
theorem interval_evolved_variation_domination
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (κ : ProbabilityTheory.Kernel X Y)
    (ph : Y → ℂ) (π : Y → Z) (_hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    (evolvedMeasure μ κ ph π).variation ≤ ((μ ⊗ₘ κ).snd).map π := by
  let Λ := (μ ⊗ₘ κ).snd
  by_cases hi : Integrable ph Λ
  · unfold evolvedMeasure
    refine VectorMeasure.variation_map_le.trans ?_
    rw [Measure.variation_withDensityᵥ hi]
    have he : (fun y => ‖ph y‖ₑ) = (fun _ : Y => (1 : ℝ≥0∞)) := by
      funext y
      simp only [← ofReal_norm, hph1 y, ENNReal.ofReal_one]
    rw [he]
    change Measure.map π (Λ.withDensity (1 : Y → ℝ≥0∞)) ≤ _
    rw [withDensity_one]
  · have hz : Λ.withDensityᵥ ph = 0 := by
      rw [Measure.withDensityᵥ, dite_eq_right hi]
    unfold evolvedMeasure
    change ((Λ.withDensityᵥ ph).map π).variation ≤ _
    rw [hz, VectorMeasure.map_zero, VectorMeasure.variation_zero]
    exact Measure.zero_le _

/-- The dominated phase-weighted evolution has finite variation for finite source and kernel. -/
theorem interval_evolved_variation_finite
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [IsFiniteMeasure μ] (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsFiniteKernel κ] (ph : Y → ℂ) (π : Y → Z)
    (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    IsFiniteMeasure (evolvedMeasure μ κ ph π).variation :=
  isFiniteMeasure_of_le _ (interval_evolved_variation_domination μ κ ph π hph hph1)

/-- Combined Fourier killing bounds control the half-time complex initial mass. -/
theorem killed_halfMeasure_mass_le {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (C k : ℝ)
    (hdec : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d),
      totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤
        ENNReal.ofReal (C * Real.exp (-k * (τ - σ) *
          (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))
    (σ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ))
    [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) :
    (halfMeasure K σ T hT.le μ ξ).variation univ ≤
      μ univ * ENNReal.ofReal (C * Real.exp
        (-(k * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) := by
  unfold halfMeasure
  refine evolved_variation_le μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
    (measurable_halfVelocity _) _ (fun x => ?_)
  refine (fibreMeasure_variation_le K hcov σ _ (le_halfTime σ T hT.le) ξ x).trans ?_
  have h := hdec σ (σ + T / 2) (le_halfTime σ T hT.le) ξ x.1.1
  have he : σ + T / 2 - σ = T / 2 := by ring
  simpa only [he, neg_mul] using h

end HypoellipticAleksandrov.KineticAleksandrov.Interval
