module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Tactic

/-! # Classicality and positivity of the canonical reflected return-time solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory SectionTwo Evolution TheoremA

/-- Reflection preserves the smooth autonomous coefficient class. -/
def returnReflectedCoefficient {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    SmoothAutonomous lam Lam :=
  ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩

/-- The canonical reflected solution is C112 on the full positive-time slab. -/
theorem reflectedSemigroupSolution_regular
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IsKineticC112On (reflectedSemigroupSolution hH hLE hlam hLam A F)
      {p | 0 < p.time} := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let G := physicalTerminalDatum (scalarTerminalDatum F)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (scalarTerminalDatum_smooth F hF).comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨u, hu, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) 0 G hG
  have heq (p : Point) (hp : 0 < p.time) :
      reflectedSemigroupSolution hH hLE hlam hLam A F p =
        u (autonomousReversal (autonomousPositionReflection p)) := by
    unfold reflectedSemigroupSolution
    dsimp only [Function.comp_apply, autonomousPositionReflection]
    rw [fullSpaceAction, dite_eq_left hp.le]
    exact (hr (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp.le)
      p.velocity (-p.position)) rfl).symm
  let O : Set Point := {p | 0 < p.time}
  let T : EvolutionVec 1 → ℝ × (PDE.Vec 1 × PDE.Vec 1) :=
    fun q => (-timeCoord 1 q, transportedCoord 1 q, -diffusedCoord 1 q)
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by unfold T; fun_prop
  have hmaps : MapsTo T (evolutionHomeomorph 1 ⁻¹' O)
      (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
    intro q hq
    refine ⟨?_, ?_⟩
    · change -timeCoord 1 q < 0
      change 0 < timeCoord 1 q at hq
      linarith
    · change transportedCoord 1 q ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
      rw [movingDomain_wholeSpace]
      trivial
  have hraw := hu.2.2.1.comp hT.contDiffOn hmaps
  apply isKineticC112On_of_contDiffOn (isOpen_lt continuous_const continuous_time)
  apply hraw.congr
  intro q hq
  exact heq (evolutionHomeomorph 1 q) hq

/-- Canonical reflected solutions satisfy every source premise for patch propagation. -/
theorem reflectedSemigroupSolution_homogeneous
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z)
    (hF0 : ∀ z, 0 ≤ F z) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IsNonnegativeHomogeneousSolution (returnReflectedCoefficient A)
      (reflectedSemigroupSolution hH hLE hlam hLam A F) := by
  obtain ⟨M, hM, hbound⟩ := F.exists_bound
  have hrep (p : Point) (hp : 0 < p.time) :
      reflectedSemigroupSolution hH hLE hlam hLam A F p =
        ∫ x, (scalarTerminalDatum F) (x.2, x.1) ∂
          (fullSpaceEvolution hH hLE hlam hLam A).2.master
            (wholeSpaceQuery 0 p.time hp.le p.velocity (-p.position)) := by
    unfold reflectedSemigroupSolution
    rw [Function.comp_apply]
    exact fullSpaceAction_eq_zeroTime A _ (fullSpaceEvolution_spec hH hLE hlam hLam A)
      _ (autonomousPositionReflection p) hp.le
  refine ⟨⟨M, ?_⟩, ?_, reflectedSemigroupSolution_regular hH hLE hlam hLam A F hF, ?_⟩
  · intro p hp
    rw [hrep p hp]
    let G := physicalTerminalDatum (scalarTerminalDatum F)
    exact abs_integral_boundedBorel_le G _
      ((fullSpaceEvolution hH hLE hlam hLam A).2.mass_le_one _) hM
      (fun x => hbound (scalarState x.swap))
  · intro p hp
    rw [hrep p hp]
    exact integral_nonneg (fun x => hF0 (scalarState x.swap))
  · intro p hp
    exact reflectedSemigroupSolution_equation hH hLE hlam hLam A F hF p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
