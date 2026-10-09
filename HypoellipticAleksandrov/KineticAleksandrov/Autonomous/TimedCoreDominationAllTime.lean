module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder

/-! # Genuine core domination by the all-time Green measure of the actual entrance count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Each actual clipped active Green kernel is bounded by the full all-time active-strip kernel. -/
theorem enlargedActiveGreenKernel_le_allTime
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (p : Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T p ≤
      enlargedActiveGreenKernel hH hLE hlam hLam A c p := by
  classical
  by_cases hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T
  · have hv : p.velocity 0 ∈ c.active :=
      ((visitActiveUnion_carrier c J).le hp.2).1
    let H := visitActiveUnion c J
    let e := enlargedVisitPole H T ⟨p, hp⟩
    let i := finiteUnionPoleIndex H T e
    have hsub : (H.component i).carrier ⊆ (visitActiveInterval c).carrier := by
      intro v hv'
      exact ((visitActiveUnion_carrier c J).le (H.component_subset i hv')).1
    have h := stripGreen_mono hH hLE hlam hLam A (H.component i) (visitActiveInterval c)
      hsub T ⊤ le_top (finiteUnionComponentPole H T e)
    change (if ht : p ∈ enlargedVisitPoleSet H T then
      finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, ht⟩) else 0) ≤
        (if ht : p.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
            (densityClockPole c p ht) else 0)
    rw [dite_eq_left hp, dite_eq_left hv]
    exact h
  · change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then _ else 0) ≤ _
    rw [dite_eq_right hp]
    intro B
    exact zero_le

/-- The genuine active Green mixture is bounded by its all-time active-strip extension. -/
theorem enlargedActiveGreenMixture_le_allTime
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (mu : Measure Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu ≤
      enlargedActiveGreen hH hLE hlam hLam A c mu := by
  unfold enlargedActiveGreen
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.bind_apply hB (Kernel.aemeasurable _)]
  exact lintegral_mono (fun p => enlargedActiveGreenKernel_le_allTime hH hLE hlam hLam A c J T p B)

/-- Core occupation is dominated by the actual all-time Green measure of the full visit count. -/
theorem enlargedOuterGreen_core_domination_of_finite_count
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P)] :
    (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} ≤
    (enlargedActiveGreen hH hLE hlam hLam A c
      (Measure.sum (enlargedVisitEntrance hH hLE hlam hLam A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core} := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  have hC : MeasurableSet C :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T hT P hP]
  unfold enlargedActiveGreen
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_tsum
  intro n
  exact Measure.restrict_mono_measure
    (enlargedActiveGreenMixture_le_allTime hH hLE hlam hLam A c J T
      (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)) C B

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
