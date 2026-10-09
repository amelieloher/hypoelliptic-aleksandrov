module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSteps
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingExit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

/-! # The initial waiting split for the actual physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The actual initial visit satisfies both outer Green and exit decompositions. -/
theorem enlargedInitial_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P 0
    let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      visitInitialGreen P (visitEntranceInterval c) GW +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      visitInitialExit P (visitEntranceInterval c) (finiteUnionExitSet J.toFiniteUnion s T) EW +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma := by
  classical
  dsimp only
  by_cases hi : P.velocity 0 ∈ closure (visitEntranceInterval c).carrier
  · simp only [enlargedVisitEntrance, visitGamma, visitInitial, visitInitialGreen,
      visitInitialExit, ite_eq_left hi, visitKernel_comp_dirac, zero_add, and_self]
  · have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
      rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
      exact sdiff_subset
    have hpw : P ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T := by
      refine ⟨hP.2.1, ?_⟩
      rw [visitWaitingUnion_carrier]
      exact ⟨hP.2.2, hi⟩
    have hmu : ∀ᵐ p ∂Measure.dirac P, p ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T :=
      (ae_dirac_iff (measurableSet_enlargedVisitPoleSet _ T)).mpr hpw
    have h := enlargedUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
      hsub s T hT (Measure.dirac P) hmu
      ((ae_dirac_iff (isClosed_le continuous_const continuous_time).measurableSet).mpr hP.1)
    simpa only [visitWaiting_internalExit, visitKernel_comp_dirac, enlargedVisitEntrance,
      visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_right hi] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
