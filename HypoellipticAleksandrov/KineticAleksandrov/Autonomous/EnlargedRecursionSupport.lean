module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalFaces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces

/-! # Actual entrance and outgoing measures satisfy the strict source-pole support -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Active outgoing pieces of the canonical enlarged alternating recursion. -/
def enlargedVisitOutgoing
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) : Measure Point :=
  visitBeta P (visitEntranceInterval c)
    (visitBoundary s T (visitEntranceInterval c) J)
    (visitBoundary s T (visitActiveInterval c) J)
    (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T)
    (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T) n

/-- Every individual outgoing piece is finite. -/
instance enlargedVisitOutgoing_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    IsFiniteMeasure (enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n) := by
  unfold enlargedVisitOutgoing
  infer_instance

/-- Incoming restriction puts every later entrance strictly inside the active spacetime strip. -/
theorem enlargedGamma_ae_activePole (P : Point) (c : Clock) (J : Interval) (s T : ℝ)
    (exitActive exitWaiting : Kernel Point Point)
    (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂visitGamma P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J)
      (visitBoundary s T (visitActiveInterval c) J) exitActive exitWaiting n,
      s ≤ p.time ∧ p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T := by
  cases n with
  | zero =>
    change ∀ᵐ p ∂visitInitial P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J) exitWaiting,
      s ≤ p.time ∧ p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T
    unfold visitInitial
    split
    · rename_i hi
      apply (ae_dirac_iff ((isClosed_le continuous_const continuous_time).measurableSet.inter
        (measurableSet_enlargedVisitPoleSet _ T))).mpr
      refine ⟨hP.1, hP.2.1, ?_⟩
      rw [visitActiveUnion_carrier]
      exact ⟨visitClosedEntrance_subset_active c hi, hP.2.2⟩
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => let h := visitIncomingFace_subset_activePole c J s T hp;
          ⟨h.1.le, h.2⟩)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
      (fun _ hp => let h := visitIncomingFace_subset_activePole c J s T hp;
          ⟨h.1.le, h.2⟩)

/-- Every active outgoing measure is supported strictly inside the waiting spacetime strip. -/
theorem enlargedBeta_ae_waitingPole (P : Point) (c : Clock) (J : Interval) (s T : ℝ)
    (exitActive exitWaiting : Kernel Point Point) (n : ℕ) :
    ∀ᵐ p ∂visitBeta P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J)
      (visitBoundary s T (visitActiveInterval c) J) exitActive exitWaiting n,
      s ≤ p.time ∧ p ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T :=
  (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
    (fun _ hp => let h := visitOutgoingFace_subset_waitingPole c J s T hp;
      ⟨h.1.le, h.2⟩)

/-- The actual entrance family satisfies the corrected nested theorem's source support. -/
theorem enlargedEntrance_ae_activePole
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n,
      s ≤ p.time ∧ p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T :=
  enlargedGamma_ae_activePole P c J s T _ _ hP n

/-- The actual outgoing family satisfies the corrected nested theorem's source support. -/
theorem enlargedOutgoing_ae_waitingPole
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n,
      s ≤ p.time ∧ p ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T :=
  enlargedBeta_ae_waitingPole P c J s T _ _ n

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
