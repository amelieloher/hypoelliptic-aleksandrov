module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces

/-! # Unconditional active and waiting steps of the physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem enlargedEntrance_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P n
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma =
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ gamma +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma =
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  have h := enlargedUnion_nested hH hLE hlam hLam A (visitActiveUnion c J) J.toFiniteUnion
    hsub s T hT (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)
    ((enlargedEntrance_ae_activePole hH hLE hlam hLam A c J s T P hP n).mono
      (fun _ hp => hp.2))
    ((enlargedEntrance_ae_activePole hH hLE hlam hLam A c J s T P hP n).mono
      (fun _ hp => hp.1))
  simpa only [visitActive_internalExit, enlargedVisitOutgoing, visitBeta,
    enlargedVisitEntrance] using h

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem enlargedOutgoing_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (n : ℕ) :
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P (n + 1)
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta =
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ beta +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta =
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  have h := enlargedUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
    hsub s T hT (enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n)
    ((enlargedOutgoing_ae_waitingPole hH hLE hlam hLam A c J s T P n).mono
      (fun _ hp => hp.2))
    ((enlargedOutgoing_ae_waitingPole hH hLE hlam hLam A c J s T P n).mono
      (fun _ hp => hp.1))
  simpa only [visitWaiting_internalExit, enlargedVisitEntrance, visitGamma,
    enlargedVisitOutgoing, visitBeta] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
