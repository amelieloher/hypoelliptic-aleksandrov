module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenTest

/-! # The actual short-time quadratic Green identity on each active component -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual localized quadratic obeys the bounded smooth Green identity. -/
theorem visitTimeQuadratic_active_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ)
    (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
    let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    f e.1 = (∫ p, f p ∂finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T e) -
      ∫ p, forwardScalarOperator A.a f p
        ∂finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T e := by
  dsimp only
  apply visitUnion_identity_bounded_smooth hH hLE hlam hLam A (visitActiveUnion c J) T e
    (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0))
  · exact visitTimeQuadratic_smooth c _ (visitTimeCutoff_properties b c.r c.positive).1
  · obtain ⟨D, _hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
    refine ⟨max (9 * c.r ^ 2 / 16) (9 * D / 16 + 2 * Lam), ?_⟩
    intro p hp
    have hv : p.velocity 0 ∈ closure c.active :=
      subset_closure ((visitActiveUnion_carrier c J).le hp).1
    have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
    have hf := visitQuadratic_nonneg c hv
    constructor
    · rw [abs_mul, abs_of_nonneg he.1, abs_of_nonneg hf]
      have hm := mul_le_mul_of_nonneg_right he.2 hf
      simp only [one_mul] at hm
      exact (hm.trans (visitQuadratic_le c _)).trans (le_max_left _ _)
    · exact (hd c b lam Lam hlam A p hv).trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
