module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIntegrated
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab

/-! # The exact localized lower weight of position-resolved starts -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The localized start integral dominates the literal cell count with weight `5*r²/16`. -/
theorem positionStartQuadratic_slab_lower (mu : Measure Point) [IsFiniteMeasure mu]
    (c : Clock) (s x a b : ℝ) (k : ℤ)
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
      ∫ p in {q : Point | s + a < q.time ∧ q.time ≤ s + b},
        positionStartCutoff (x + ((k : ℝ) + 1 / 2) * c.r ^ 3) c.r c.positive
          (p.position 0) * visitQuadratic c (p.velocity 0) ∂mu := by
  let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
  let f := fun p : Point => positionStartCutoff Y c.r c.positive (p.position 0) *
    visitQuadratic c (p.velocity 0)
  let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
  let B := {p : Point | s + a < p.time ∧ p.time ≤ s + b ∧
    p.position 0 ∈ enlargedPositionCell c.r x k ∧
      p.velocity 0 ∈ closure c.entrance}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hB : MeasurableSet B :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      ((isClosed_le continuous_time continuous_const).measurableSet.inter
        (((measurableSet_enlargedPositionCell c.r x k).preimage
          ((continuous_apply 0).comp continuous_position).measurable).inter
            (isClosed_closure.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable)))
  have hf : Integrable f mu := positionStartQuadratic_integrable c Y mu
    (hmu.mono fun _ hp => subset_closure (enlarged_closedEntrance_subset_active c hp))
  have hm : (∫ p, B.indicator (fun _ => 5 * c.r ^ 2 / 16) p ∂mu) ≤
      ∫ p, S.indicator f p ∂mu := by
    apply integral_mono_ae ((integrable_const _).indicator hB) (hf.indicator hS)
    filter_upwards [hmu] with p hv
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ S from ⟨hp.1, hp.2.1⟩)]
      exact positionStartQuadratic_start_lower c x k p hp.2.2.1 hp.2.2.2
    · rw [indicator_of_notMem hp]
      by_cases hs : p ∈ S
      · rw [indicator_of_mem hs]
        exact mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
          (visitQuadratic_nonneg c
            (subset_closure (enlarged_closedEntrance_subset_active c hv)))
      · rw [indicator_of_notMem hs]
  rw [integral_indicator hB, integral_const, integral_indicator hS] at hm
  change 5 * c.r ^ 2 / 16 * (mu B).toReal ≤ ∫ p in S, f p ∂mu
  simpa only [smul_eq_mul, mul_comm, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
