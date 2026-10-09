module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationEnlarged

/-! # The cylinder core domination and continuation conclusions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

/-- The genuine cylinder continuation disappears without a count-finiteness premise. -/
theorem visit_continuation_vanishes
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    Tendsto (fun n => (visitUnionGreenKernel hH hLE hlam hLam A
      (capacityCylinderInterval Z0 R hR).toFiniteUnion Z0.time (Z0.time + R ^ 2) ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c (capacityCylinderInterval Z0 R hR)
          Z0.time (Z0.time + R ^ 2) P n) univ) atTop (𝓝 0) :=
  visitOuterGreen_remainder_tendsto_zero hH hLE hlam hLam A c
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) P (visitCylinderStart_mem Z0 R hR P hP)

/-- The original cylinder strip Green is dominated on the core by the actual visit Green measure. -/
theorem core_green_le_visitGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP)).restrict
        {q | q.velocity 0 ∈ c.core} := by
  have hp := visitCylinderStart_mem Z0 R hR P hP
  have hd := visitOuterGreen_core_domination hH hLE hlam hLam A c
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) P hp
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A _ _ _ P hp] at hd
  exact hd

/-- Active partial occupation is dominated by the outer Green restricted to active velocities. -/
theorem visitActiveGreen_partial_le_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n ≤
    (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P).restrict
      {q | q.velocity 0 ∈ c.active} := by
  have h := Measure.restrict_mono_measure
    (visitActiveGreen_partial_le hH hLE hlam hLam A c J s T hT P hP N)
    {q | q.velocity 0 ∈ c.active}
  rw [visit_restrict_finset_sum] at h
  have he (n : ℕ) :
      (visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
          {q | q.velocity 0 ∈ c.active} =
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n :=
    Measure.restrict_eq_self_of_ae_mem
    (visitActiveGreenMixture_ae_active hH hLE hlam hLam A c J s T
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n))
  simpa only [he] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
