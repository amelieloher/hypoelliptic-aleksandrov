module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

/-! # Unconditional finite alternating Green and exit identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The actual Green kernels satisfy the source's finite alternating identity. -/
theorem visitAlternating_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let GA := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let GO := visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P
    GO P = visitInitialGreen P (visitEntranceInterval c) GW +
      ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N := by
  apply alternating_green_of_nested_splitting
  · exact (visitInitial_nested hH hLE hlam hLam A c J s T hT P hP).1
  · intro n
    exact (visitEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).1
  · intro n
    exact (visitOutgoing_nested hH hLE hlam hLam A c J s T hT P n).1

/-- The actual exit kernels satisfy the source's finite alternating identity. -/
theorem visitAlternating_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let EA := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let EW := visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let EO := visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    EO P = visitInitialExit P (visitEntranceInterval c) outer EW +
      ∑ n ∈ Finset.range N,
        ((EA ∘ₘ gamma n).restrict outer + (EW ∘ₘ beta n).restrict outer) +
          EO ∘ₘ gamma N := by
  apply alternating_exit_of_nested_splitting
  · exact (visitInitial_nested hH hLE hlam hLam A c J s T hT P hP).2
  · intro n
    exact (visitEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).2
  · intro n
    exact (visitOutgoing_nested hH hLE hlam hLam A c J s T hT P n).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
