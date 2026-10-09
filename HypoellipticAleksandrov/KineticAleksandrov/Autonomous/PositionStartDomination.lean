module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartMassBound
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation

/-! # Passing actual finite-piece occupation domination to the canonical starting measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical ENNReal

/-- Domination of every initial partial sum dominates the complete positive measure sum. -/
theorem positionStart_sum_le_of_partial_le {X : Type*} [MeasurableSpace X]
    (mu : ℕ → Measure X) (nu : Measure X)
    (h : ∀ N : ℕ, (∑ n ∈ Finset.range N, mu n) ≤ nu) : Measure.sum mu ≤ nu := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  simpa only [Measure.finsetSum_apply, hB] using h N B

/-- On a slab ending before the horizon, the genuine all-time active Green is its finite one. -/
theorem positionStartGreen_slab_eq_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b U : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (hv : p.velocity 0 ∈ c.active) (hp : p.time < U) (hb : b ≤ U) :
    (coreAllTimeGreenKernel hH hLE hlam hLam A c p).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} =
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) U p).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} := by
  have he : coreAllTimeGreenKernel hH hLE hlam hLam A c p =
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
    change (if h : p.velocity 0 ∈ c.active then _ else (0 : Measure Point)) = _
    rw [dite_eq_left hv]
    rfl
  rw [he, positionStartGreen_eq_restrict hH hLE hlam hLam A c J U hJ p hv hp]
  have hS : MeasurableSet {q : Point | a < q.time ∧ q.time ≤ b} :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  rw [Measure.restrict_restrict hS]
  apply Measure.restrict_congr_set
  filter_upwards [positionStartGreen_ae_time_ne hH hLE hlam hLam A c p hv U] with q hq
  apply propext
  constructor
  · intro h
    exact ⟨h, lt_of_le_of_ne (h.2.trans hb) hq⟩
  · exact fun h => h.1

/-- Restricting actual starting mixtures preserves the finite-horizon slab identity. -/
theorem positionStartGreenMixture_slab_eq_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b U : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active ∧ p.time < U) (hb : b ≤ U) :
    (coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} =
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) U ∘ₘ mu).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} := by
  let S := {q : Point | a < q.time ∧ q.time ≤ b}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
    Measure.bind_apply (hB.inter hS) (Kernel.aemeasurable _),
    Measure.bind_apply (hB.inter hS) (Kernel.aemeasurable _)]
  apply lintegral_congr_ae
  filter_upwards [hmu] with p hp
  have h := congrArg (fun rho : Measure Point => rho B)
    (positionStartGreen_slab_eq_finite hH hLE hlam hLam A c J a b U hJ p hp.1 hp.2 hb)
  simpa only [Measure.restrict_apply hB] using h

/-- All actual active occupations are dominated by full-space occupation. -/
theorem positionStart_all_occupation_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hT : 0 < T) (hv : P.velocity 0 ∈ J.carrier) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + T) ∘ₘ
      enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T := by
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  change (Measure.sum mu).bind
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + T)) ≤ _
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _)]
  apply positionStart_sum_le_of_partial_le
  exact enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
