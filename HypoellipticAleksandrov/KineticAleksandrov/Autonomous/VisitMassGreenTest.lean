module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalDomains
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMeasures

/-! # The actual bounded quadratic Green identity on each active component -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Bounded smooth physical tests obey the Green identity on actual finite unions. -/
theorem visitUnion_identity_bounded_smooth
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ (KineticPoint.equivProd 1).symm))
    (hb : ∃ M : ℝ, ∀ p, p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂finiteUnionExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂finiteUnionGreen hH hLE hlam hLam A H T e := by
  apply strip_identity_bounded_smooth hH hLE hlam hLam A
    (H.component (finiteUnionPoleIndex H T e)) T (finiteUnionComponentPole H T e) phi hphi
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, fun p hp => hM p (H.component_subset _ hp)⟩

/-- The source quadratic is uniformly bounded together with its operator on the active union. -/
theorem visitQuadratic_active_bounded {lam Lam : ℝ} (hlam : 0 < lam)
    (_hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) :
    ∃ M : ℝ, ∀ p : Point, p.velocity 0 ∈ (visitActiveUnion c J).carrier →
      |visitQuadratic c (p.velocity 0)| ≤ M ∧
      |forwardScalarOperator A.a (fun q => visitQuadratic c (q.velocity 0)) p| ≤ M := by
  refine ⟨max (9 * c.r ^ 2 / 16) (2 * Lam), ?_⟩
  intro p hp
  have hv : p.velocity 0 ∈ closure c.active :=
    subset_closure ((visitActiveUnion_carrier c J).le hp).1
  constructor
  · rw [abs_of_nonneg (visitQuadratic_nonneg c hv)]
    exact (visitQuadratic_le c _).trans (le_max_left _ _)
  · rw [visitQuadratic_operator]
    have ha := A.bounds (p.position 0) (p.velocity 0)
    rw [abs_of_nonpos (by nlinarith [ha.1])]
    exact (by nlinarith [ha.2] : -(-2 * A.a (p.position 0) (p.velocity 0)) ≤ 2 * Lam).trans
      (le_max_right _ _)

/-- The genuine active-component quadratic identity, before any visit summation. -/
theorem visitQuadratic_active_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
    visitQuadratic c (e.1.velocity 0) =
      (∫ p, visitQuadratic c (p.velocity 0)
        ∂finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T e) -
      ∫ p, -2 * A.a (p.position 0) (p.velocity 0)
        ∂finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T e := by
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : Point => visitQuadratic c (q.velocity 0)) ∘
        (KineticPoint.equivProd 1).symm) :=
    (visitQuadratic_smooth c).comp
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.snd)
  simpa only [visitQuadratic_operator] using
    visitUnion_identity_bounded_smooth hH hLE hlam hLam A (visitActiveUnion c J) T e
      (fun q => visitQuadratic c (q.velocity 0)) hs
      (visitQuadratic_active_bounded hlam hLam A c J)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
