module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitBorel

/-! # The compact smooth Green identity for the uniquely characterized exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The actual compact smooth identity, with the prescribed physical operator and signs. -/
theorem strip_identity_compact_smooth_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hcompact : HasCompactSupport phi) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  let f : exitProbeSubmodule :=
    ⟨phi ∘ reconstructionPhysicalHomeomorph, hphi,
      hcompact.comp_homeomorph reconstructionPhysicalHomeomorph⟩
  have heq : exitProbePhysical f = phi := by
    funext p
    exact congrArg phi (reconstructionPhysicalHomeomorph.apply_symm_apply p)
  have hi := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e f
  unfold exitProbeValue at hi
  rw [heq] at hi
  linarith

/-- The compact smooth identity in the source's raw physical product coordinates. -/
theorem strip_identity_compact_smooth_raw_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ (KineticPoint.equivProd 1).symm))
    (hcompact : HasCompactSupport phi) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  apply strip_identity_compact_smooth_of_realization hH hlam hLam A H E hE T e phi
    _ hcompact
  let c : EvolutionVec 1 → ℝ × PDE.Vec 1 × PDE.Vec 1 :=
    fun x => ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2,
      (evolutionProdCLE 1 x).2.1)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (evolutionProdCLE 1).contDiff.fst.prodMk
      ((evolutionProdCLE 1).contDiff.snd.snd.prodMk
        (evolutionProdCLE 1).contDiff.snd.fst)
  have heq : (phi ∘ (KineticPoint.equivProd 1).symm) ∘ c =
      phi ∘ reconstructionPhysicalHomeomorph := by
    funext x
    rfl
  rw [← heq]
  exact hphi.comp hc

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
