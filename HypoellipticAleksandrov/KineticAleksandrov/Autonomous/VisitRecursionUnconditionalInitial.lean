module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSteps
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingExit

/-! # The initial waiting split for the actual physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Composing any physical kernel with a point mass evaluates that kernel. -/
theorem visitKernel_comp_dirac (k : Kernel Point Point) (P : Point) :
    k ∘ₘ Measure.dirac P = k P := Measure.dirac_bind k.measurable P

/-- The actual initial visit satisfies both outer Green and exit decompositions. -/
theorem visitInitial_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P 0
    let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let EW := visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      visitInitialGreen P (visitEntranceInterval c) GW +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      visitInitialExit P (visitEntranceInterval c) (finiteUnionExitSet J.toFiniteUnion s T) EW +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by
  classical
  dsimp only
  by_cases hi : P.velocity 0 ∈ closure (visitEntranceInterval c).carrier
  · simp only [visitEntrancePiece, visitGamma, visitInitial, visitInitialGreen,
      visitInitialExit, ite_eq_left hi, visitKernel_comp_dirac, zero_add, and_self]
  · have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
      rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
      exact sdiff_subset
    have hpw : P ∈ visitPoleSet (visitWaitingUnion c J) s T := by
      refine ⟨hP.1, hP.2.1, ?_⟩
      rw [visitWaitingUnion_carrier]
      exact ⟨hP.2.2, hi⟩
    have hmu : ∀ᵐ p ∂Measure.dirac P, p ∈ visitPoleSet (visitWaitingUnion c J) s T :=
      (ae_dirac_iff (measurableSet_visitPoleSet _ s T)).mpr hpw
    have h := visitUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
      hsub s T hT (Measure.dirac P) hmu
    simpa only [visitWaiting_internalExit, visitKernel_comp_dirac, visitEntrancePiece,
      visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_right hi] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
