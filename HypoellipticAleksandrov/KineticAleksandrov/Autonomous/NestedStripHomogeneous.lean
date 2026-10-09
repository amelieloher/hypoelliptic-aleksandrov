module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical

/-! # Genuine bounded homogeneous potentials of compact exit probes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic

/-- The actual reconstruction of a compact probe has a uniform closed-slab bound and
the actual exit representation at every pole in that slab. -/
theorem exists_nested_homogeneous_potential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ) (hT : sMinus < T)
    (f : exitProbeSubmodule) :
    ∃ u : Point → ℝ,
      IsKineticC112On u (reconstructionStrip H (sMinus - 1) T) ∧
      (∀ p ∈ reconstructionStrip H (sMinus - 1) T, forwardScalarOperator A.a u p = 0) ∧
      ContinuousOn u (reconstructionClosedSlab H sMinus T) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H sMinus T, |u p| ≤ C) ∧
      EqOn u (exitProbePhysical f) (reconstructionExit H (sMinus - 1) T) ∧
      (∀ e : StripPole H (T : WithTop ℝ), sMinus ≤ e.1.time →
        u e.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H T e) := by
  let E := stripEvolution hH hLE hlam hLam A H
  have hE := stripEvolution_spec hH hLE hlam hLam A H
  have hphi := exitProbePhysical_isKineticC112On f
    (reconstructionStrip H (sMinus - 1) T) (isOpen_reconstructionStrip H _ T)
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H (sMinus - 1) T,
      |exitProbePhysical f p| ≤ M ∧
        |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := ⟨M, fun p _ => hM p⟩
  obtain ⟨u, hform, hu, hop, hc, htrace⟩ := strip_bounded_source_reconstruction
    hH hlam hLam A H E hE (sMinus - 1) T (exitProbePhysical f) hphi
      (exitProbePhysical_continuous_compact f).1.continuousOn hb
  let p : Point := ⟨sMinus, 0, fun _ => (H.lo + H.hi) / 2⟩
  have hv : p.velocity 0 ∈ H.carrier := by
    change H.lo < (H.lo + H.hi) / 2 ∧ (H.lo + H.hi) / 2 < H.hi
    constructor <;> linarith [H.ordered]
  let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hT, hv⟩
  have he : sMinus - 1 < e.1.time := by change sMinus - 1 < sMinus; linarith
  have hbound := reconstruction_uniform_bound H E A (sMinus - 1) T e he
    (exitProbePhysical f) u hphi hb hform hc
  refine ⟨u, nested_raw_isKineticC112On (isOpen_reconstructionStrip H _ T) hu,
    hop, hc.mono (reconstructionClosedSlab_subset_strip_union_exit H he),
    hbound, htrace, ?_⟩
  intro ep hep
  have hepl : sMinus - 1 < ep.1.time := by linarith
  have hvalue := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T ep f
  have hformula := hform ep hepl
  rw [integral_neg] at hformula
  change (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H T ep) =
    exitProbePhysical f ep.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
      ∂stripGreenOfKernel H E.2 T ep at hvalue
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
