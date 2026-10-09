module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalKernels

/-! # No-loss conversion from physical measures to subtype pole mixtures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Pulling a supported physical measure to its pole subtype and mapping it back loses no mass. -/
theorem visitPoleMeasure_map_comap (D : Set Point) (hD : MeasurableSet D)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ D) :
    (mu.comap (Subtype.val : D → Point)).map Subtype.val = mu := by
  rw [map_comap_subtype_coe hD, Measure.restrict_eq_self_of_ae_mem hmu]

/-- Zero-extended kernel composition agrees with the mixture on the physical pole subtype. -/
theorem visitExtendKernel_comp (D : Set Point) (hD : MeasurableSet D)
    (f : D → Measure Point) (hf : Measurable f)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ D) :
    visitExtendKernel D hD f hf ∘ₘ mu = (mu.comap (Subtype.val : D → Point)).bind f := by
  let nu := mu.comap (Subtype.val : D → Point)
  have hm : nu.map Subtype.val = mu := visitPoleMeasure_map_comap D hD mu hmu
  let k := visitExtendKernel D hD f hf
  change k ∘ₘ mu = nu.bind f
  rw [← hm]
  ext B hB
  rw [Measure.bind_apply hB k.aemeasurable,
    lintegral_map (k.measurable_coe hB) measurable_subtype_coe,
    Measure.bind_apply hB hf.aemeasurable]
  apply lintegral_congr
  intro p
  change (if hp : p.1 ∈ D then f ⟨p.1, hp⟩ else 0) B = f p B
  rw [dite_eq_left p.2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
