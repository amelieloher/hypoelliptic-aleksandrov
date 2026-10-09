module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical

/-! # The actual larger-strip source potential restricted to the smaller strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The genuine larger-strip compact-source potential satisfies the smaller-strip identity.
The strict lower-time condition is the source's open-strip hypothesis. -/
theorem nestedSourcePotential_small_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier}) :
    (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
      ∫ p, nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f p
        ∂stripExit hH hLE hlam hLam A H1 T e := by
  let E := stripEvolution hH hLE hlam hLam A H2
  have hE := stripEvolution_spec hH hLE hlam hLam A H2
  let u := nestedSourcePotential H2 E T f
  obtain ⟨⟨C, -, hC⟩, hu, hop⟩ :=
    nestedSourcePotential_regular_source hH hlam hLam A H2 E hE T f hfn hs
  have hc := (nestedSourcePotential_continuous_zero_exit
    hH hlam hLam A H2 E hE T f hfn hs).1
  have hi : reconstructionStrip H1 sMinus T ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier} :=
    fun _ hp => ⟨hp.2.1, hsub hp.2.2⟩
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H1 sMinus T,
      |u p| ≤ M ∧ |forwardScalarOperator A.a u p| ≤ M := by
    refine ⟨max C M, fun p hp => ⟨(hC p).trans (le_max_left _ _), ?_⟩⟩
    rw [hop p (hi hp).1 (hi hp).2, abs_neg]
    exact (hM p).1.trans (le_max_right _ _)
  have ht : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
  have hsmall : Parabolic.IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
    ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
      fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
      hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
      hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
  have hid := strip_identity_C112 hH hLE hlam hLam A H1 sMinus T
    (he.trans ht) e he u hsmall
    (hc.mono (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T)) hb
  have hg : (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen hH hLE hlam hLam A H1 T e] fun p => -exitProbePhysical f p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
      (stripEvolution hH hLE hlam hLam A H1).2 T e] with p hp
    exact hop p hp.1 (hsub hp.2)
  rw [integral_congr_ae hg, integral_neg] at hid
  have hr := nestedSourcePotential_eq_green A H2 E T f
    (nestedPoleInclusion H1 H2 hsub T e)
  change u e.1 = ∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
    (nestedPoleInclusion H1 H2 hsub T e) at hr
  rw [← hr]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
