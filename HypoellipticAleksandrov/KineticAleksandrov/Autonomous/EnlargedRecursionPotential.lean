module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPotentialIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates

/-! # Full-space classical potentials in physical coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- Full-space evolution supplies every regularity and positivity premise of stopped tests. -/
theorem enlarged_exists_fullspace_potential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (b : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF0 : ∀ z, 0 ≤ F z) :
    ∃ u : Point → ℝ, IsKineticC112On u {p | p.time < b} ∧
      ContinuousOn u {p | p.time ≤ b} ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ p, p.time ≤ b → |u p| ≤ M) ∧
      (∀ p, p.time < b → forwardScalarOperator A.a u p = 0) ∧
      (∀ p, p.time ≤ b → 0 ≤ u p) ∧
      (∀ p, p.time = b → u p = F (p.velocity, p.position)) ∧
      (∀ p (hp : p.time ≤ b), u p = ∫ z, F z ∂
        (fullSpaceEvolution hH hLE hlam hLam A).2.master
          (wholeSpaceQuery p.time b hp p.velocity p.position)) := by
  obtain ⟨v, hv, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A
    (fullSpaceEvolution hH hLE hlam hLam A)
    (fullSpaceEvolution_spec hH hLE hlam hLam A) b F hF
  have hwhole (t : ℝ) : movingDomain autonomousWholeDomain (fun _ => 0) t = univ :=
    movingDomain_wholeSpace 1 t
  let u := v ∘ sectionTwoPoint
  have hm (p : Point) (hp : p.time ≤ b) : sectionTwoPoint p ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) b := by
    refine ⟨hp, ?_⟩
    rw [hwhole, closure_univ]
    trivial
  have hc : ContinuousOn u {p | p.time ≤ b} := hv.2.1.comp
    (continuous_sectionTwoPoint 1).continuousOn (fun p hp => hm p hp)
  have hs : IsKineticC112On u {p | p.time < b} := by
    apply nested_raw_isKineticC112On (isOpen_lt continuous_time continuous_const)
    let g : ℝ × (PDE.Vec 1 × PDE.Vec 1) → ℝ × (PDE.Vec 1 × PDE.Vec 1) :=
      fun q => (q.1, q.2.2, q.2.1)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := by unfold g; fun_prop
    have hmaps : MapsTo g ((KineticPoint.equivProd 1) '' {p : Point | p.time < b})
        (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) b) := by
      rintro q ⟨p, hp, rfl⟩
      refine ⟨hp, ?_⟩
      rw [hwhole]
      trivial
    exact hv.2.2.1.comp hg.contDiffOn hmaps
  have hrep (p : Point) (hp : p.time ≤ b) : u p = ∫ z, F z ∂
      (fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery p.time b hp p.velocity p.position) :=
    hr (wholeSpaceQuery p.time b hp p.velocity p.position) rfl
  refine ⟨u, hs, hc, ?_, ?_, ?_, ?_, hrep⟩
  · obtain ⟨M, hM, hb⟩ := hv.1
    exact ⟨M, hM, fun p hp => hb _ (hm p hp)⟩
  · intro p hp
    have hmem : sectionTwoPoint p ∈ evolutionPastOpenCylinder
        autonomousWholeDomain (fun _ => 0) b := by
      refine ⟨hp, ?_⟩
      rw [hwhole]
      trivial
    have ho := hv.2.2.2.1 (sectionTwoPoint p) hmem
    have he : v = u ∘ sectionTwoPoint := by
      funext q
      exact congrArg v (sectionTwoPoint_involutive q).symm
    rw [he, reconstruction_scalar_operator_swap, sectionTwoPoint_involutive p] at ho
    exact ho
  · intro p hp
    rw [hrep p hp]
    exact integral_nonneg hF0
  · intro p hp
    exact hv.2.2.2.2.1 (sectionTwoPoint p) ⟨hp, by
      rw [hwhole, closure_univ]
      trivial⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
