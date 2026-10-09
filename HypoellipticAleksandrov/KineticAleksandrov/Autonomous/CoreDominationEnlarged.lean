module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCylinderCount

/-! # Core domination for visits in the enlarged bounded outer interval -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Enlarging the outer interval gives the literal core domination by its own visit starts. -/
theorem visitSmallerOuterGreen_core_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Jsmall J : Interval)
    (hsub : Jsmall.carrier ⊆ J.carrier) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ Jsmall.carrier) :
    (stripGreen hH hLE hlam hLam A Jsmall T
      ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩).restrict {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core} := by
  have hp : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier :=
    ⟨hP.1, hP.2.1, hsub hP.2.2⟩
  have hm := stripGreen_mono hH hLE hlam hLam A Jsmall J hsub T T le_rfl
    ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩
  have hd := visitOuterGreen_core_domination hH hLE hlam hLam A c J s T hT P hp
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A J s T P hp] at hd
  exact (Measure.restrict_mono_measure hm _).trans hd

/-- The timed-entrance core conclusion uses the actual enlarged-strip counting measure. -/
theorem timedEntrance_core_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (_hbar : c.vbar = 2 * c.r ∨ c.vbar = -2 * c.r)
    (Z0 : Point) (R : ℝ) (hR : 0 < R) (J : Interval)
    (hJ : closure (capacityCylinderInterval Z0 R hR).carrier ⊆ J.carrier)
    (_hactive : closure c.active ⊆ J.carrier) (P : Point)
    (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J Z0.time
        (Z0.time + R ^ 2) P))).restrict {q | q.velocity 0 ∈ c.core} :=
  visitSmallerOuterGreen_core_domination hH hLE hlam hLam A c
    (capacityCylinderInterval Z0 R hR) J (fun _ hv => hJ (subset_closure hv))
    Z0.time (Z0.time + R ^ 2) (by nlinarith [sq_pos_of_pos hR]) P
      (visitCylinderStart_mem Z0 R hR P hP)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
