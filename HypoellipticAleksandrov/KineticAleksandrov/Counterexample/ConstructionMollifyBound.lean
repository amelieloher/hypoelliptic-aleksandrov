module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity

/-! # Essential bounds suffice for normalized spatial convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped Convolution

/-- The normalized mollifier respects an essential bound, without changing the selected
representative on its exceptional null set. -/
theorem construction_spatialMollify_norm_le_ae {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
    [FiniteDimensional ℝ G] [Measure.IsAddHaarMeasure (volume : Measure G)]
    (phi : ContDiffBump (0 : G)) (g : G → ℝ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂volume, |g x| ≤ C) (q : G) :
    ‖spatialMollify phi g q‖ ≤ C := by
  let f := fun x => max (-C) (min (g x) C)
  have hf : AEStronglyMeasurable f volume :=
    (aemeasurable_const.max (hg.aemeasurable.min aemeasurable_const)).aestronglyMeasurable
  have he : f =ᵐ[volume] g := by
    filter_upwards [hb] with x hx
    have hh := abs_le.mp hx
    simp only [f, min_eq_left hh.2, max_eq_right hh.1]
  have hfB : ∀ x, ‖f x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (neg_le_self hC) (min_le_right _ _)
  have hc : spatialMollify phi f = spatialMollify phi g := by
    exact convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.Eventually.of_forall (fun _ => rfl)) he
  rw [← hc]
  exact spatialMollify_norm_le phi f hf C hC hfB q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
