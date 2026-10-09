module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount

/-! # The source's cylinder entrance count and its uniform radius dependence -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- A forward-cylinder start has the literal strict physical pole support used by visits. -/
theorem visitCylinderStart_mem (Z0 : Point) (R : ℝ) (hR : 0 < R) (P : Point)
    (hP : P ∈ forwardCylinder Z0 R hR) :
    Z0.time < P.time ∧ P.time < Z0.time + R ^ 2 ∧
      P.velocity 0 ∈ (capacityCylinderInterval Z0 R hR).carrier :=
  ⟨hP.1, hP.2.1, (capacityCylinderPole Z0 P R hR hP).2.2⟩

/-- The actual cylinder counting measure is finite. -/
theorem visitStartsQ_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    IsFiniteMeasure (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP) :=
  visitCount_isFiniteMeasure hH hLE hlam hLam A c (capacityCylinderInterval Z0 R hR)
    Z0.time (Z0.time + R ^ 2) (by nlinarith [sq_pos_of_pos hR]) P
      (visitCylinderStart_mem Z0 R hR P hP)

/-- One ellipticity constant bounds every actual cylinder count by `C * (1 + R / r)`. -/
theorem exists_visitStartsQ_mass_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP univ ≤
          ENNReal.ofReal (C * (1 + R / c.r)) := by
  obtain ⟨C, hC, hc⟩ := exists_visitCount_mass_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c Z0 R hR P hP
  have h := hc hH hLE A c (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) P (visitCylinderStart_mem Z0 R hR P hP)
  have hw : ((capacityCylinderInterval Z0 R hR).hi -
      (capacityCylinderInterval Z0 R hR).lo) / 2 = R := by
    dsimp only [capacityCylinderInterval]
    ring
  simpa only [hw, visitStartsQ] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
