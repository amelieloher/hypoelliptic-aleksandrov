module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReconstructionTracesContinuity

/-! # Actual bounded-source homogeneous reconstruction on a finite strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The physical scalar operator is the native transported operator after coordinate exchange. -/
theorem reconstruction_scalar_operator_swap (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (u ∘ sectionTwoPoint) p = forwardScalarOperator a u (sectionTwoPoint p) := by
  rw [transportedForwardOperator_apply, forwardScalarOperator]
  simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
    evolutionCoefficient, PDE.vecDot, identityDrift]
  change kineticTimeDerivative u (sectionTwoPoint p) +
      a (p.velocity 0) (p.position 0) * kineticVelocityHessian u (sectionTwoPoint p) 0 0 +
      p.position 0 * kineticPositionGradient u (sectionTwoPoint p) 0 = _
  dsimp only [sectionTwoPoint]
  ring

/-- The packed operator depends only on the function germ, including its second derivatives. -/
theorem reconstruction_transportedOperator_congr
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    {u f : EvolutionVec 1 → ℝ} {x : EvolutionVec 1} (h : u =ᶠ[𝓝 x] f) :
    transportedOperator B b u x = transportedOperator B b f x := by
  have hd := h.fderiv_eq (𝕜 := ℝ)
  have hh (j : Fin 1) :
      (fun y => fderiv ℝ u y (basisV j)) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ f y (basisV j)) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  unfold transportedOperator
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hh j).fderiv_eq (𝕜 := ℝ)]

/-- A bounded C112 test has an actual smooth homogeneous reconstruction, with the prescribed
exit values and the literal Green integral at every strictly interior pole. -/
theorem strip_bounded_source_reconstruction
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ u : Point → ℝ,
      (∀ e : StripPole H (T : WithTop ℝ), sMinus < e.1.time →
        u e.1 = phi e.1 - ∫ p, -forwardScalarOperator A.a phi p
          ∂stripGreenOfKernel H E.2 T e) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
        (KineticPoint.equivProd 1 '' reconstructionStrip H sMinus T) ∧
      (∀ p ∈ reconstructionStrip H sMinus T, forwardScalarOperator A.a u p = 0) ∧
      ContinuousOn u (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T) ∧
      EqOn u phi (reconstructionExit H sMinus T) := by
  obtain ⟨g, f, hg, hg0, hf, heq, hop⟩ :=
    exists_reconstruction_smooth_pointwise hH hlam hLam A H E hE sMinus T phi hphi hb
  let u := stripReconstructionCandidate H E.2 T phi g
  let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
  have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
    continuous_reconstructionPhysicalPoint
  have hus : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ reconstructionPhysicalPoint) U :=
    hf.congr (fun x hx => heq hx)
  have huop : ∀ x ∈ U, transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
      (u ∘ reconstructionPhysicalPoint) x = 0 := by
    intro x hx
    have hh : (u ∘ reconstructionPhysicalPoint) =ᶠ[𝓝 x] f :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => heq hy)
    rw [reconstruction_transportedOperator_congr _ _ hh]
    exact hop x hx
  refine ⟨u, ?_, ?_, ?_,
    reconstruction_candidate_continuousOn_exit hH hlam hLam A H E hE sMinus T phi hphi hc g hg,
    stripReconstructionCandidate_eqOn_exit H E.2 sMinus T phi g⟩
  · intro e he
    have hgAE : g =ᵐ[stripGreenOfKernel H E.2 T e] fun p => -forwardScalarOperator A.a phi p := by
      filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
        reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
      exact hg p ⟨he.trans ht, hp⟩
    change phi e.1 - stripSourcePotential H E.2 T g e.1 = _
    rw [stripSourcePotential_eq_green H E.2 T g e]
    exact congrArg (fun z => phi e.1 - z) (integral_congr_ae hgAE)
  · let c : (ℝ × PDE.Vec 1 × PDE.Vec 1) → EvolutionVec 1 :=
      fun q => (evolutionProdCLE 1).symm (q.1, q.2.2, q.2.1)
    have hcs : ContDiff ℝ (⊤ : ℕ∞) c :=
      (evolutionProdCLE 1).symm.contDiff.comp
        (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))
    have hec : (fun q => reconstructionPhysicalPoint (c q)) =
        (KineticPoint.equivProd 1).symm := by
      funext q
      simp [c, reconstructionPhysicalPoint, KineticPoint.equivProd]
    have hmaps : MapsTo c (KineticPoint.equivProd 1 '' reconstructionStrip H sMinus T) U := by
      rintro q ⟨p, hp, rfl⟩
      change reconstructionPhysicalPoint (c (KineticPoint.equivProd 1 p)) ∈
        reconstructionStrip H sMinus T
      rw [congrFun hec, Equiv.symm_apply_apply]
      exact hp
    have hh := hus.comp hcs.contDiffOn hmaps
    have heqf : (u ∘ reconstructionPhysicalPoint) ∘ c = u ∘ (KineticPoint.equivProd 1).symm := by
      funext q
      change u (reconstructionPhysicalPoint (c q)) = _
      rw [congrFun hec]
      rfl
    rwa [heqf] at hh
  · intro p hp
    let x := (evolutionHomeomorph 1).symm (sectionTwoPoint p)
    have hxp : reconstructionPhysicalPoint x = p := by
      change sectionTwoPoint (evolutionHomeomorph 1 x) = p
      rw [Homeomorph.apply_symm_apply, sectionTwoPoint_involutive]
    have hx : x ∈ U := by
      change reconstructionPhysicalPoint x ∈ reconstructionStrip H sMinus T
      rwa [hxp]
    have hsm : ContDiffAt ℝ 2 ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x :=
      (hus.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
    have hh := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hsm
    change transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
      (u ∘ reconstructionPhysicalPoint) x =
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
          (u ∘ sectionTwoPoint) (evolutionHomeomorph 1 x) at hh
    rw [huop x hx] at hh
    rw [Homeomorph.apply_symm_apply, reconstruction_scalar_operator_swap,
      sectionTwoPoint_involutive] at hh
    exact hh.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
