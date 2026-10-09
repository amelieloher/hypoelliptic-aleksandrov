module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReconstructionTracesRepresentative

/-! # Pointwise identification of the actual homogeneous reconstruction

Continuity of the actual source potential upgrades the smooth representative's AE equality
on the open strip. No representative or classical source solver is an input hypothesis.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The actual negative-operator source is continuous in native product coordinates. -/
theorem reconstruction_source_continuousOn
    {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) :
    ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T) := by
  have hc : ContinuousOn g (reconstructionStrip H sMinus T) :=
    ((continuousOn_forwardScalarOperator A hphi).neg).congr (fun p hp => hg p hp)
  apply hc.comp ((continuous_sectionTwoPoint 1).comp
    (KineticPoint.homeomorphProd 1).symm.continuous).continuousOn
  intro x hx
  exact hx

/-- The smooth homogeneous representative equals the literal candidate everywhere inside. -/
theorem reconstruction_candidate_eq_smooth
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p)
    (f : EvolutionVec 1 → ℝ)
    (hf : ContinuousOn f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T))
    (hae : (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
      =ᵐ[volume.restrict
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f) :
    EqOn (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint) f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) := by
  have hp := reconstruction_source_potential_continuousOn hH hlam hLam A H E hE
    sMinus T g (reconstruction_source_continuousOn A H sMinus T phi hphi g hg)
  have hc : ContinuousOn (stripReconstructionCandidate H E.2 T phi g)
      (reconstructionStrip H sMinus T) := hphi.continuousOn.sub hp
  have hcp := hc.comp continuous_reconstructionPhysicalPoint.continuousOn (fun _ hx => hx)
  exact Measure.eqOn_open_of_ae_eq hae
    ((isOpen_reconstructionStrip H sMinus T).preimage continuous_reconstructionPhysicalPoint)
    hcp hf

/-- An actual bounded-source reconstruction has a smooth homogeneous representative with
pointwise equality at every strictly interior source point. -/
theorem exists_reconstruction_smooth_pointwise
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      EqOn (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
  obtain ⟨g, f, hg, hg0, hf, hae, heq⟩ :=
    exists_reconstruction_smooth_ae hH hlam A H E hE sMinus T phi hphi hb
  exact ⟨g, f, hg, hg0, hf,
    reconstruction_candidate_eq_smooth hH hlam hLam A H E hE sMinus T phi hphi g hg
      f hf.continuousOn hae, heq⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
