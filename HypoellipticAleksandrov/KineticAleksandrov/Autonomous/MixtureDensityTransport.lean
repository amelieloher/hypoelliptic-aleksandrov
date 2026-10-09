module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityDuality
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Transport of density estimates through kinetic coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory
open scoped ENNReal

/-- A measurable coordinate map commutes with multiplication by a pulled-back density. -/
theorem mixture_map_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) (f : X → Y) (hf : Measurable f) (w : Y → ℝ≥0∞)
    (hw : Measurable w) :
    (m.withDensity (w ∘ f)).map f = (m.map f).withDensity w := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg hf]
  change (∫⁻ x, (g ∘ f) x ∂m.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul m (hw.comp hf) (hg.comp hf),
    lintegral_withDensity_eq_lintegral_mul (m.map f) hw hg,
    lintegral_map (hw.mul hg) hf]
  rfl

/-- Bounded conjugate tests on kinetic points yield their actual-volume density estimate. -/
theorem mixture_point_density_of_tests (mu : Measure (KineticPoint 1))
    [IsFiniteMeasure mu] (q C : ℝ) (hq : 1 < q) (hC : 0 ≤ C)
    (htest : ∀ f : BoundedBorel (KineticPoint 1),
      MemLp f (ENNReal.ofReal (q / (q - 1))) volume → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C *
        (eLpNorm f (ENNReal.ofReal (q / (q - 1))) volume).toReal) :
    ∃ g : KineticPoint 1 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      mu = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g (ENNReal.ofReal q) volume ∧
      (eLpNorm g (ENNReal.ofReal q) volume).toReal ≤ C := by
  let F := KineticPoint.equivProd 1
  have hm := KineticPoint.measurable_equivProd 1
  have hp : MeasurePreserving F volume volume :=
    KineticPoint.measurePreserving_equivProd 1
  have he : MeasurableEmbedding F := (KineticPoint.homeomorphProd 1).measurableEmbedding
  have : (volume : Measure (PDE.Vec 1 × PDE.Vec 1)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have : (volume : Measure (ℝ × (PDE.Vec 1 × PDE.Vec 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have ht : ∀ f : BoundedBorel (ℝ × (PDE.Vec 1 × PDE.Vec 1)),
      MemLp f (ENNReal.ofReal (q / (q - 1))) volume → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu.map F) ≤ C *
        (eLpNorm f (ENNReal.ofReal (q / (q - 1))) volume).toReal := by
    intro f hfp hfn
    have hh := htest (f.pullback F hm) (hfp.comp_measurePreserving hp)
      (fun x => hfn (F x))
    change (∫ x, f (F x) ∂mu) ≤ C *
      (eLpNorm ((↑f) ∘ F) (ENNReal.ofReal (q / (q - 1))) volume).toReal at hh
    rw [he.integral_map f]
    simpa only [eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable hp] using hh
  obtain ⟨g, hgm, hgn, hgd, hgp, hgb⟩ :=
    mixture_density_bound_of_bounded_tests volume (mu.map F) q C hq hC ht
  refine ⟨g ∘ F, hgm.comp hm, fun x => hgn (F x), ?_,
    hgp.comp_measurePreserving hp, ?_⟩
  · apply he.map_injective
    change mu.map F = (volume.withDensity ((fun x => ENNReal.ofReal (g x)) ∘ F)).map F
    rw [mixture_map_withDensity volume F hm _ hgm.ennreal_ofReal, hp.map_eq]
    exact hgd
  · simpa only [eLpNorm_comp_measurePreserving hgp.aestronglyMeasurable hp] using hgb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
