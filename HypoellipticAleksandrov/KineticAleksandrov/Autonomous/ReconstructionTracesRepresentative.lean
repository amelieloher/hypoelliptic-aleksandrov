module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionBounds

/-! # Exit traces of the actual homogeneous smooth AE representative

The test continuity and the proved potential barriers supply the prescribed
terminal and lateral traces of the smooth representative. No pointwise identity
between that representative and the Green reconstruction is assumed or concluded.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Evolution MeasureTheory Set Filter
open scoped Topology

/-- A continuous homogeneous AE representative has the prescribed trace at every exit. -/
theorem reconstruction_representative_exit_tendsto
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hc : ContinuousOn phi
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C)
    (f : EvolutionVec 1 → ℝ)
    (hf : ContinuousOn f
      (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T))
    (hae : (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
      =ᵐ[volume.restrict
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f)
    (x : ℕ → EvolutionVec 1)
    (hx : ∀ n, reconstructionPhysicalPoint (x n) ∈ reconstructionStrip H sMinus T)
    (p : Point) (hp : p ∈ reconstructionExit H sMinus T)
    (hxp : Tendsto (fun n => reconstructionPhysicalPoint (x n)) atTop (𝓝 p)) :
    Tendsto (fun n => f (x n)) atTop (𝓝 (phi p)) := by
  have hφ : Tendsto (fun n => phi (reconstructionPhysicalPoint (x n))) atTop (𝓝 (phi p)) :=
    (hc p (Or.inr hp)).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hxp
        (Eventually.of_forall fun n => Or.inl (hx n)))
  have hb := reconstruction_representative_barriers hH hlam hLam A H E hE sMinus T
    phi (hc.mono subset_union_left) g C hC hg f hf hae
  have hzero : Tendsto (fun n => f (x n) - phi (reconstructionPhysicalPoint (x n)))
      atTop (𝓝 0) := by
    rcases hp with ht | hv
    · have htime : Tendsto (fun n => timeCoord 1 (x n)) atTop (𝓝 p.time) :=
        continuous_time.tendsto p |>.comp hxp
      have hbound : Tendsto (fun n => C * (T - timeCoord 1 (x n))) atTop (𝓝 0) := by
        have htend : Tendsto (fun n => C * (T - timeCoord 1 (x n))) atTop
            (𝓝 (C * (T - p.time))) :=
          tendsto_const_nhds.mul (tendsto_const_nhds.sub htime)
        simpa only [ht.1, sub_self, mul_zero] using htend
      exact squeeze_zero_norm (fun n => by
        simpa only [Real.norm_eq_abs] using (hb (x n) (hx n)).1) hbound
    · have hvel := ((continuous_apply 0).comp continuous_velocity).tendsto p |>.comp hxp
      have hbound : Tendsto (fun n => C * ((diffusedCoord 1 (x n) 0 - H.lo) *
          (H.hi - diffusedCoord 1 (x n) 0) / (2 * lam))) atTop
          (𝓝 (C * ((p.velocity 0 - H.lo) * (H.hi - p.velocity 0) / (2 * lam)))) :=
        tendsto_const_nhds.mul
          (((hvel.sub_const H.lo).mul (tendsto_const_nhds.sub hvel)).div_const (2 * lam))
      have hbound0 : Tendsto (fun n => C * ((diffusedCoord 1 (x n) 0 - H.lo) *
          (H.hi - diffusedCoord 1 (x n) 0) / (2 * lam))) atTop (𝓝 0) := by
        rcases hv.2.2 with hl | hh
        · simpa only [hl, sub_self, zero_mul, mul_zero, zero_div] using hbound
        · simpa only [hh, sub_self, zero_mul, mul_zero, zero_div] using hbound
      exact squeeze_zero_norm (fun n => by
        simpa only [Real.norm_eq_abs] using (hb (x n) (hx n)).2) hbound0
  have h := hzero.add hφ
  simpa only [sub_add_cancel, zero_add] using h

/-- The source test hypotheses construct a smooth homogeneous AE reconstruction
with the prescribed traces at every terminal or velocity exit point. -/
theorem exists_reconstruction_smooth_ae_with_exit_traces
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : Parabolic.IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
        =ᵐ[volume.restrict
          (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f ∧
      (∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (SectionTwo.identityDrift 1) f x = 0) ∧
      ∀ (x : ℕ → EvolutionVec 1),
        (∀ n, reconstructionPhysicalPoint (x n) ∈ reconstructionStrip H sMinus T) →
        ∀ p ∈ reconstructionExit H sMinus T,
          Tendsto (fun n => reconstructionPhysicalPoint (x n)) atTop (𝓝 p) →
          Tendsto (fun n => f (x n)) atTop (𝓝 (phi p)) := by
  obtain ⟨g, f, hg, hg0, hf, hae, heq⟩ :=
    exists_reconstruction_smooth_ae hH hlam A H E hE sMinus T phi hphi hb
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  exact ⟨g, f, hg, hg0, hf, hae, heq, fun x hx p hp hxp =>
    reconstruction_representative_exit_tendsto hH hlam hLam A H E hE sMinus T phi
      hc g C hC hgb f hf.continuousOn hae x hx p hp hxp⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
