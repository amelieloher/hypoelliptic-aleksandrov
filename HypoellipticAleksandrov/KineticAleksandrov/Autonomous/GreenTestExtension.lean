module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit

/-! # The full actual finite-strip Green identity for the original bounded C112 class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution

/-- The original bounded C112 class has the full actual identity at every strictly interior
starting time, with no extra regularity or boundary-solution premise. -/
theorem strip_identity_C112_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (_hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  obtain ⟨u, hform, hu, hop, huc, hexit⟩ := strip_bounded_source_reconstruction
    hH hlam hLam A H E hE sMinus T phi hphi hc hb
  have hub := reconstruction_uniform_bound H E A sMinus T e he phi u hphi hb hform huc
  have hrep := reconstruction_homogeneous_exit_representation hH hlam hLam A H E hE
    sMinus T e he u hu hop huc hub
  have hclosed : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e
  have hAE : u =ᵐ[stripExitOfRealization hH hlam hLam A H E hE T e] phi := by
    filter_upwards [hclosed,
      stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e] with p hp ht
    apply hexit
    rcases hp with hp | hp
    · exact Or.inl hp
    · by_cases hpt : p.time = T
      · exact Or.inl ⟨hpt, ht.2.2⟩
      · exact Or.inr ⟨he.trans_le ht.1, lt_of_le_of_ne hp.1 hpt, hp.2⟩
  rw [integral_congr_ae hAE] at hrep
  have hh := hform e he
  rw [integral_neg] at hh
  linarith

/-- The canonical autonomous families satisfy the full C112 identity at an interior pole. -/
theorem strip_identity_C112
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ) (hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H T e :=
  strip_identity_C112_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) sMinus T hT e he phi hphi hc hb

/-- A start at the named lower endpoint is covered by regularity on a strictly lower strip,
exactly as the endpoint convention requires. -/
theorem strip_identity_C112_lowered
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (lower sMinus T : ℝ)
    (hlower : lower < sMinus) (hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H lower T))
    (hc : ContinuousOn phi (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H lower T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H T e :=
  strip_identity_C112 hH hLE hlam hLam A H lower T (hlower.trans hT) e
    (hlower.trans_le he) phi hphi hc hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
