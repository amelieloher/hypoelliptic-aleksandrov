module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Tactic

/-! # The literal angular density tail estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The finite weighted angular mass is the source tail integrability for its actual density. -/
theorem bellmanAngularDensity_tail (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F)
    (f : ℝ → ℝ) (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : LocallyIntegrable f volume) (hn : ∀ᵐ x ∂volume, 0 ≤ f x) :
    IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  let S : Set ℝ := {y | 2 < |y|}
  have hS : MeasurableSet S := by measurability
  have hm : Measurable (fun y : ℝ => |y| ^ (β - 4)) := by fun_prop
  have hi : IntegrableOn (fun y : ℝ => |y| ^ (β - 4)) S F := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ fun y => Real.rpow_nonneg (abs_nonneg y) _)).mp
    exact (bellmanAngularTail_lintegral_finite β μ F hrep).ne
  have hfm := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [hF, IntegrableOn, restrict_withDensity hS] at hi
  have ht := (integrable_withDensity_iff_integrable_smul₀' hfm.restrict
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).mp hi
  apply ht.congr
  filter_upwards [ae_restrict_of_ae hn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov
