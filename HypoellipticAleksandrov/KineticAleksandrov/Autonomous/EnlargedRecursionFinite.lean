module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionInitial

/-! # Unconditional finite alternating Green and exit identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The actual Green kernels satisfy the source's finite alternating identity. -/
theorem enlargedAlternating_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
    GO P = visitInitialGreen P (visitEntranceInterval c) GW +
      ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N := by
  apply alternating_green_of_nested_splitting
  · exact (enlargedInitial_nested hH hLE hlam hLam A c J s T hT P hP).1
  · intro n
    exact (enlargedEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).1
  · intro n
    exact (enlargedOutgoing_nested hH hLE hlam hLam A c J s T hT P n).1

/-- The actual exit kernels satisfy the source's finite alternating identity. -/
theorem enlargedAlternating_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let EO := enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    EO P = visitInitialExit P (visitEntranceInterval c) outer EW +
      ∑ n ∈ Finset.range N,
        ((EA ∘ₘ gamma n).restrict outer + (EW ∘ₘ beta n).restrict outer) +
          EO ∘ₘ gamma N := by
  apply alternating_exit_of_nested_splitting
  · exact (enlargedInitial_nested hH hLE hlam hLam A c J s T hT P hP).2
  · intro n
    exact (enlargedEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).2
  · intro n
    exact (enlargedOutgoing_nested hH hLE hlam hLam A c J s T hT P n).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
