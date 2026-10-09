module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionMarginal
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierGreen

/-! # The interval Green measure on the zero-extension carrier

The measure itself is unchanged. Only the initial-state measure is pushed forward
under the literal inclusion of the interval fiber.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green

/-- An interval Green measure satisfies the adapted whole-carrier characterization. -/
theorem intervalExtension_isGreenMeasure {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ : ℝ) (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)) (hΓ : IsGreenMeasure K σ ⊤ μ Γ) :
    IsGreenMeasure (intervalExtension hJ K) σ ⊤ (μ.map (intervalStateInclusion σ)) Γ := by
  intro F hF
  let Kw := intervalExtension hJ K
  have : ProbabilityTheory.IsFiniteKernel (elapsedKernel Kw σ ⊤) := by
    unfold elapsedKernel
    infer_instance
  have hf : Measurable (fun q :
      (EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤) ×
        EvolutionAmbientState 1 => F (q.1.2, q.2)) := hF.comp (by fun_prop)
  have hi : Measurable (fun q :
      EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤ =>
      ∫⁻ w, F (q.2, w) ∂elapsedKernel Kw σ ⊤ q) :=
    hf.lintegral_kernel_prod_right'
  have hm : Measurable (fun p :
      EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ =>
      ∫⁻ t : ElapsedTime ⊤, ∫⁻ w, F (t, w) ∂Kw.master (elapsedQuery σ p t)
        ∂elapsedVolume ⊤) := hi.lintegral_prod_right'
  rw [lintegral_map hm (measurable_intervalStateInclusion σ), hΓ F hF]
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall fun p => ?_
  dsimp only
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall fun t => ?_
  dsimp only
  change (∫⁻ w, F (t, w) ∂K.master (elapsedQuery σ p t)) =
    ∫⁻ w, F (t, w) ∂intervalExtensionMaster hJ K
      (intervalQueryInclusion (elapsedQuery σ p t))
  rw [intervalExtensionMaster_inside]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
