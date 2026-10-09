module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal

/-! # The genuine position-localized Green test on each active visit -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The position-localized quadratic is smooth in the physical product coordinates. -/
theorem positionStartQuadratic_smooth (c : Clock) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : Point => eta (q.position 0) * visitQuadratic c (q.velocity 0)) ∘
        (KineticPoint.equivProd 1).symm) :=
  (heta.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.fst)).mul
    ((visitQuadratic_smooth c).comp
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.snd))

/-- The actual position test satisfies the Green identity, with no analytic bridge premise. -/
theorem positionStartQuadratic_active_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y T : ℝ)
    (hc : |c.vbar| = 2 * c.r)
    (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    f e.1 = (∫ p, f p ∂finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T e) -
      ∫ p, forwardScalarOperator A.a f p
        ∂finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T e := by
  dsimp only
  apply visitUnion_identity_bounded_smooth hH hLE hlam hLam A (visitActiveUnion c J) T e
    (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0))
  · exact positionStartQuadratic_smooth c _
      (positionStartCutoff_properties Y c.r c.positive).1
  · obtain ⟨C, hC, hb⟩ := positionStartQuadratic_operator_bound hlam hLam
    refine ⟨max (9 * c.r ^ 2 / 16) C, ?_⟩
    intro p hp
    have hv := ((visitActiveUnion_carrier c J).le hp).1
    have hchi := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
    have hquad := visitQuadratic_nonneg c (subset_closure hv)
    constructor
    · rw [abs_mul, abs_of_nonneg hchi.1, abs_of_nonneg hquad]
      exact ((mul_le_mul_of_nonneg_right hchi.2 hquad).trans
        (by simpa only [one_mul] using visitQuadratic_le c (p.velocity 0))).trans
          (le_max_left _ _)
    · apply (hb A c Y p hc hv).trans
      by_cases hbox : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
      · rw [indicator_of_mem hbox, mul_one]
        exact le_max_right _ _
      · rw [indicator_of_notMem hbox, mul_zero]
        exact hC.le.trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
