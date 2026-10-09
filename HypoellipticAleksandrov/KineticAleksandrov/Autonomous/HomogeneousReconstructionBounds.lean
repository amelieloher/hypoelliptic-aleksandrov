module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionDistribution

/-! # Pointwise barrier bounds for the homogeneous smooth representative

Continuity upgrades the almost-everywhere barrier inequalities to pointwise
inequalities. This does not upgrade the Green formula itself to pointwise equality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Evolution MeasureTheory Set

private theorem continuousOn_le_of_ae {U : Set (EvolutionVec 1)} (hU : IsOpen U)
    {f b : EvolutionVec 1 → ℝ} (hf : ContinuousOn f U) (hb : ContinuousOn b U)
    (hae : f ≤ᵐ[volume.restrict U] b) : ∀ x ∈ U, f x ≤ b x := by
  have heq : (fun x => max (f x) (b x)) =ᵐ[volume.restrict U] b := by
    filter_upwards [hae] with x hx
    exact max_eq_right hx
  have h := Measure.eqOn_open_of_ae_eq heq hU (hf.sup hb) hb
  intro x hx
  exact (le_max_left (f x) (b x)).trans_eq (h hx)

/-- Every continuous representative inherits both actual Green-potential barriers. -/
theorem reconstruction_representative_barriers
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T))
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C)
    (f : EvolutionVec 1 → ℝ)
    (hf : ContinuousOn f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T))
    (hae : (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
      =ᵐ[volume.restrict
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f) :
    ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
      |f x - phi (reconstructionPhysicalPoint x)| ≤
        C * (T - timeCoord 1 x) ∧
      |f x - phi (reconstructionPhysicalPoint x)| ≤
        C * ((diffusedCoord 1 x 0 - H.lo) * (H.hi - diffusedCoord 1 x 0) / (2 * lam)) := by
  let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
  let b₁ : EvolutionVec 1 → ℝ := fun x => C * (T - timeCoord 1 x)
  let b₂ : EvolutionVec 1 → ℝ := fun x =>
    C * ((diffusedCoord 1 x 0 - H.lo) * (H.hi - diffusedCoord 1 x 0) / (2 * lam))
  have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
    continuous_reconstructionPhysicalPoint
  have hd : ContinuousOn (fun x => |f x - phi (reconstructionPhysicalPoint x)|) U :=
    (hf.sub (hc.comp continuous_reconstructionPhysicalPoint.continuousOn
      (fun _ hx => hx))).abs
  have hb₁ : Continuous b₁ :=
    continuous_const.mul (continuous_const.sub (timeCoord 1).continuous)
  have hv : Continuous (fun x : EvolutionVec 1 => diffusedCoord 1 x 0) :=
    (continuous_apply 0).comp (diffusedCoord 1).continuous
  have hb₂ : Continuous b₂ :=
    continuous_const.mul ((hv.sub continuous_const).mul
      (continuous_const.sub hv) |>.div_const (2 * lam))
  have hpoint (x : EvolutionVec 1) (hx : x ∈ U) :
      |stripReconstructionCandidate H E.2 T phi g (reconstructionPhysicalPoint x) -
        phi (reconstructionPhysicalPoint x)| ≤ b₁ x ∧
      |stripReconstructionCandidate H E.2 T phi g (reconstructionPhysicalPoint x) -
        phi (reconstructionPhysicalPoint x)| ≤ b₂ x := by
    let p := reconstructionPhysicalPoint x
    let e : StripPole H (T : WithTop ℝ) :=
      ⟨p, WithTop.coe_lt_coe.mpr hx.2.1, hx.2.2⟩
    have h₁ := stripPotentialOfKernel_abs_le H E.2 T g e C hC hg
    have h₂ := stripPotentialOfRealization_abs_le_quadratic hH hlam hLam A H E hE
      T e g C hC hg
    have heq : |stripReconstructionCandidate H E.2 T phi g p - phi p| =
        |stripPotentialOfKernel H E.2 T g e| := by
      rw [stripReconstructionCandidate]
      have hh : phi p - stripSourcePotential H E.2 T g p - phi p =
          -stripSourcePotential H E.2 T g p := by ring
      rw [hh, abs_neg, stripSourcePotential_eq_green H E.2 T g e]
    exact ⟨heq.trans_le h₁, heq.trans_le h₂⟩
  have h₁ : (fun x => |f x - phi (reconstructionPhysicalPoint x)|)
      ≤ᵐ[volume.restrict U] b₁ := by
    filter_upwards [hae, ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [← hx]
    exact (hpoint x hxU).1
  have h₂ : (fun x => |f x - phi (reconstructionPhysicalPoint x)|)
      ≤ᵐ[volume.restrict U] b₂ := by
    filter_upwards [hae, ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [← hx]
    exact (hpoint x hxU).2
  exact fun x hx =>
    ⟨continuousOn_le_of_ae hU hd hb₁.continuousOn h₁ x hx,
      continuousOn_le_of_ae hU hd hb₂.continuousOn h₂ x hx⟩

/-- The constructed source and smooth homogeneous representative obey the exact
time and velocity-face barriers, with no assumed interior continuity of the potential. -/
theorem exists_reconstruction_smooth_ae_with_barriers
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : Parabolic.IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ) (C : ℝ),
      0 ≤ C ∧ (∀ p, |g p| ≤ C) ∧
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
        =ᵐ[volume.restrict
          (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f ∧
      (∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (SectionTwo.identityDrift 1) f x = 0) ∧
      ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        |f x - phi (reconstructionPhysicalPoint x)| ≤ C * (T - timeCoord 1 x) ∧
        |f x - phi (reconstructionPhysicalPoint x)| ≤
          C * ((diffusedCoord 1 x 0 - H.lo) * (H.hi - diffusedCoord 1 x 0) / (2 * lam)) := by
  obtain ⟨g, f, hg, hg0, hf, hae, heq⟩ :=
    exists_reconstruction_smooth_ae hH hlam A H E hE sMinus T phi hphi hb
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  exact ⟨g, f, C, hC, hgb, hg, hg0, hf, hae, heq,
    reconstruction_representative_barriers hH hlam hLam A H E hE sMinus T phi
      hphi.continuousOn g C hC hgb f hf.continuousOn hae⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
