module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport

/-! # Independence of the named lower observation time below the initial pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- A supported exit mixture stays strictly later than a common lower pole bound. -/
theorem enlargedExitMixture_ae_time_gt_lower
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T L : ℝ)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L ≤ p.time) :
    ∀ᵐ q ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu), L < q.time := by
  apply Measure.ae_comp_of_ae_ae
    (isOpen_lt continuous_const continuous_time).measurableSet
  filter_upwards [hmu] with p hp
  exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
    fun q hq => hp.trans_lt hq

/-- Below a supported exit time, changing the named observation lower bound changes no face. -/
theorem enlargedBoundary_restrict_lower_eq (I J : Interval) (s L T : ℝ) (hs : s ≤ L)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L < p.time) :
    mu.restrict (visitBoundary s T I J) = mu.restrict (visitBoundary L T I J) := by
  apply Measure.restrict_congr_set
  filter_upwards [hmu] with p hp
  have hsp := hs.trans_lt hp
  simp only [visitBoundary, mem_ofPred_eq, hsp, hp, true_and]

/-- Canonical entrance pieces depend on the actual initial time, not an earlier named cutoff. -/
theorem enlargedVisitEntrance_lower_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    enlargedVisitEntrance hH hLE hlam hLam A c J s T P n =
      enlargedVisitEntrance hH hLE hlam hLam A c J P.time T P n := by
  let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  induction n with
  | zero =>
    unfold enlargedVisitEntrance visitGamma visitInitial
    split
    · rfl
    · exact enlargedBoundary_restrict_lower_eq _ _ s P.time T hs _
        (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A (visitWaitingUnion c J) T P)
  | succ n ih =>
    change (EW ∘ₘ ((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
      (visitBoundary s T (visitActiveInterval c) J))).restrict
        (visitBoundary s T (visitEntranceInterval c) J) =
      (EW ∘ₘ ((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J P.time T P n).restrict
        (visitBoundary P.time T (visitActiveInterval c) J))).restrict
          (visitBoundary P.time T (visitEntranceInterval c) J)
    rw [ih]
    have hgamma := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J
      P.time T P le_rfl hT n).mono fun _ hp => hp.1
    have hA := enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
      (visitActiveUnion c J) T P.time _ hgamma
    have hbeta := enlargedBoundary_restrict_lower_eq (visitActiveInterval c) J s P.time T hs _ hA
    change (EA ∘ₘ _).restrict _ = _ at hbeta
    rw [hbeta]
    have hsrc : ∀ᵐ p ∂((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J P.time T P n).restrict
        (visitBoundary P.time T (visitActiveInterval c) J)), P.time ≤ p.time :=
      (ae_restrict_mem (measurableSet_visitBoundary P.time T (visitActiveInterval c) J)).mono
        fun _ hp => hp.1.le
    exact enlargedBoundary_restrict_lower_eq _ _ s P.time T hs _
      (enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
        (visitWaitingUnion c J) T P.time _ hsrc)

/-- The full enlarged counting measure is unchanged by lowering the observation cutoff. -/
theorem enlargedVisitStarts_lower_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) :
    enlargedVisitStarts hH hLE hlam hLam A c J s T P =
      enlargedVisitStarts hH hLE hlam hLam A c J P.time T P := by
  unfold enlargedVisitStarts
  congr 1
  funext n
  exact enlargedVisitEntrance_lower_eq hH hLE hlam hLam A c J s T P hs hT n

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
