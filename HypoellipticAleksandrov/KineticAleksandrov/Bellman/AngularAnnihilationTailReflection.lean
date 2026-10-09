module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTail
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-! # Reflection of the finite angular tail -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Reflection preserves the two-sided density-tail integrability condition. -/
theorem bellmanAngularTail_reflect (β : ℝ) (f : ℝ → ℝ)
    (ht : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    IntegrableOn (fun y => f (-y) * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  have hi := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).mpr ht
  have he : (fun y : ℝ => -y) ⁻¹' {y : ℝ | 2 < |y|} = {y : ℝ | 2 < |y|} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, abs_neg]
  rw [he] at hi
  apply hi.congr_fun _ (by measurability)
  intro y _
  change f (-y) * |-y| ^ (β - 4) = f (-y) * |y| ^ (β - 4)
  rw [abs_neg]

/-- An almost everywhere comparison on the real line holds after reflection. -/
theorem bellmanAngularComparison_reflect (R : ℝ) (f h : ℝ → ℝ)
    (hc : ∀ᵐ y ∂volume, h y ≤ R * f y) :
    ∀ᵐ y ∂volume, h (-y) ≤ R * f (-y) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hc

end HypoellipticAleksandrov.KineticAleksandrov
