module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreenTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt

/-! # The exact Green measure decomposition for nested physical velocity intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual larger Green measure is the smaller Green plus the actual internal restart Green. -/
theorem nestedIntervalGreen_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    stripGreen hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) =
      stripGreen hH hLE hlam hLam A H1 T e +
        nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e := by
  let D := stripPast H2 T
  have hs (ep : StripPole H2 (T : WithTop ℝ)) :
      ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H2 T ep, p ∈ D :=
    stripGreenOfKernel_ae_mem_stripPast H2 (stripEvolution hH hLE hlam hLam A H2).2 T ep
  have hsmall : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H1 T e, p ∈ D := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
      (stripEvolution hH hLE hlam hLam A H1).2 T e] with p hp
    exact ⟨hp.1, hsub hp.2⟩
  have hrestart : ∀ᵐ p ∂nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e,
      p ∈ D := by
    rw [ae_iff]
    unfold nestedIntervalRestartGreen
    refine (Measure.bind_apply (m := nestedIntervalRestartPoles hH hLE hlam hLam A
      H1 H2 sMinus T e) (isOpen_stripPast H2 T).measurableSet.compl
      (Measure.measurable_measure.mpr (fun B hB =>
        stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB)).aemeasurable).trans ?_
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall (fun ep => ae_iff.mp (hs ep))
  apply nested_physical_measure_eq D (isOpen_stripPast H2 T)
    (hs (nestedPoleInclusion H1 H2 hsub T e))
  · rw [ae_iff, Measure.add_apply, ae_iff.mp hsmall, ae_iff.mp hrestart]
    exact zero_add 0
  · intro f hfs hfn
    rw [integral_add_measure (nestedProbe_integrable A f _)
      (nestedProbe_integrable A f _)]
    exact nestedIntervalGreen_probe_identity hH hLE hlam hLam A H1 H2 hsub
      sMinus T e he f hfn hfs

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
