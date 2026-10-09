module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCylinderCount

/-! # The source entrance-mass theorem for actual cylinder visits -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The source entrance count bound, with a constant depending only on ellipticity. -/
theorem visit_total_mass {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR)
        (_hcore : (c.core ∩ (capacityCylinderInterval Z0 R hR).carrier).Nonempty),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP univ ≤
          ENNReal.ofReal (C * (1 + R / c.r)) := by
  obtain ⟨C, hC, hc⟩ := exists_visitStartsQ_mass_constant hlam hLam
  exact ⟨C, hC, fun hH hLE A c Z0 R hR P hP _ => hc hH hLE A c Z0 R hR P hP⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
