module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCylinderCount

/-! # The source short-time entrance estimate, including the initial atom -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- A closed time window includes an initial visit even when it is at the lower endpoint. -/
theorem visit_short_time_mass_closed {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) (b : ℝ),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
          {p | p.time ∈ Icc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := exists_visitTime_mass_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c Z0 R hR P hP b
  exact hc hH hLE A c (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2) b
    (by nlinarith [sq_pos_of_pos hR]) P (visitCylinderStart_mem Z0 R hR P hP)

/-- The literal source half-open short-time window satisfies the same uniform count bound. -/
theorem visit_short_time_mass {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) (b : ℝ),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
          {p | p.time ∈ Ioc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := visit_short_time_mass_closed hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c Z0 R hR P hP b
  have hs : {p : Point | p.time ∈ Ioc b (b + c.r ^ 2)} ⊆
      {p | p.time ∈ Icc b (b + c.r ^ 2)} := fun _ hp => ⟨hp.1.le, hp.2⟩
  exact (measure_mono hs).trans (hc hH hLE A c Z0 R hR P hP b)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
