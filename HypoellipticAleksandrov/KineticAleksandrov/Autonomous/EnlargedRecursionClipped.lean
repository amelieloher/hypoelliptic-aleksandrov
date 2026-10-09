module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionLower
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount

/-! # Equality with a strictly earlier clipped recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- On poles after `s`, the enlarged exit kernel agrees with a finite clipped kernel. -/
theorem enlargedVisitExit_comp_eq_clipped
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ)
    (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
    enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu =
      visitUnionExitKernel hH hLE hlam hLam A H (s - 1) T ∘ₘ mu := by
  classical
  apply Measure.comp_congr
  filter_upwards [hs] with p hp
  change (if h : p ∈ enlargedVisitPoleSet H T then
    finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩) else 0) =
      (if h : p ∈ visitPoleSet H (s - 1) T then
        finiteUnionExit hH hLE hlam hLam A H T
          (visitPoleInclusion H (s - 1) T ⟨p, h⟩) else 0)
  have he : p ∈ enlargedVisitPoleSet H T ↔ p ∈ visitPoleSet H (s - 1) T := by
    change (p.time < T ∧ p.velocity 0 ∈ H.carrier) ↔
      (s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier)
    constructor
    · intro h
      exact ⟨by linarith, h⟩
    · exact fun h => h.2
  by_cases h : p ∈ enlargedVisitPoleSet H T
  · rw [dite_eq_left h, dite_eq_left (he.mp h)]
    rfl
  · rw [dite_eq_right h, dite_eq_right (fun hh => h (he.mpr hh))]

/-- Lowering the clipped cutoff strictly below the initial pole preserves every entrance. -/
theorem enlargedVisitEntrance_eq_clipped
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    enlargedVisitEntrance hH hLE hlam hLam A c J s T P n =
      visitEntrancePiece hH hLE hlam hLam A c J (s - 1) T P n := by
  let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  have he (H : FiniteIntervalUnion) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s ≤ p.time) :=
    enlargedVisitExit_comp_eq_clipped hH hLE hlam hLam A H s T mu hm
  have hb (I : Interval) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s < p.time) :
      mu.restrict (visitBoundary s T I J) =
        mu.restrict (visitBoundary (s - 1) T I J) :=
    (enlargedBoundary_restrict_lower_eq I J (s - 1) s T (by linarith) mu hm).symm
  induction n with
  | zero =>
    unfold enlargedVisitEntrance visitEntrancePiece visitGamma visitInitial
    split
    · rfl
    · have hm : ∀ᵐ p ∂Measure.dirac P, s ≤ p.time :=
        (ae_dirac_iff (isClosed_le continuous_const continuous_time).measurableSet).mpr hs
      have hx := he (visitWaitingUnion c J) (Measure.dirac P) hm
      simp only [visitKernel_comp_dirac] at hx
      rw [← hx]
      exact hb _ _ ((enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A
        (visitWaitingUnion c J) T P).mono fun _ hp => hs.trans_lt hp)
  | succ n ih =>
    change (EW ∘ₘ ((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
      (visitBoundary s T (visitActiveInterval c) J))).restrict
        (visitBoundary s T (visitEntranceInterval c) J) = _
    have hg := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
      fun _ hp => hp.1
    have ha := enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
      (visitActiveUnion c J) T s _ hg
    have hbeta : ∀ᵐ p ∂((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
        (visitBoundary s T (visitActiveInterval c) J)), s ≤ p.time :=
      (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
        fun _ hp => hp.1.le
    have hw := enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
      (visitWaitingUnion c J) T s _ hbeta
    rw [hb _ _ hw, he _ _ hbeta, hb _ _ ha, he _ _ hg, ih]
    rfl

/-- The actual enlarged count is finite for every valid outer-strip initial pole. -/
theorem enlargedVisitStarts_finite_of_outer_pole
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P) := by
  have he : enlargedVisitStarts hH hLE hlam hLam A c J s T P =
      Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J (s - 1) T P) := by
    unfold enlargedVisitStarts
    congr 1
    funext n
    exact enlargedVisitEntrance_eq_clipped hH hLE hlam hLam A c J s T P hP.1 hP.2.1 n
  rw [he]
  exact visitCount_isFiniteMeasure hH hLE hlam hLam A c J (s - 1) T (by linarith [hP.1])
    P ⟨by linarith [hP.1], hP.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
