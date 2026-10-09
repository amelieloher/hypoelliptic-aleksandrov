module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Summing the literal position-resolved visit cells

Source: companion paper, Lemma 8.6. These identities hold for any finite measure and
preserve the entrance restriction and the initial time-bin convention.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- Each position-resolved visit cell is measurable. -/
theorem measurableSet_enlargedPositionVisitCell (c : Clock) (s x : ℝ)
    (j : ℕ) (k : ℤ) :
    MeasurableSet (enlargedStartCell c s x j k ∩
      {p | p.velocity 0 ∈ closure c.entrance}) :=
  (measurableSet_enlargedStartCell c s x j k).inter
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Position cells partition the entrance-supported portion of one time bin. -/
theorem iUnion_enlargedPositionVisitCell (c : Clock) (s x : ℝ) (j : ℕ) :
    (⋃ k : ℤ, enlargedStartCell c s x j k ∩
      {p | p.velocity 0 ∈ closure c.entrance}) =
      {p | p.time ∈ enlargedTimeBin c.r s j ∧ p.velocity 0 ∈ closure c.entrance} := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact ⟨hk.1.1, hk.2⟩
  · intro hp
    obtain ⟨k, hk⟩ := enlargedPositionCell_covers c.r x (p.position 0) c.positive
    exact mem_iUnion.mpr ⟨k, ⟨⟨hp.1, hk⟩, hp.2⟩⟩

/-- Distinct position-resolved visit cells in one time bin are disjoint. -/
theorem pairwiseDisjoint_enlargedPositionVisitCell (c : Clock) (s x : ℝ) (j : ℕ) :
    Pairwise (fun k l : ℤ => Disjoint
      (enlargedStartCell c s x j k ∩ {p | p.velocity 0 ∈ closure c.entrance})
      (enlargedStartCell c s x j l ∩ {p | p.velocity 0 ∈ closure c.entrance})) := by
  intro k l hkl
  apply disjoint_left.mpr
  intro p hk hl
  exact disjoint_left.mp (enlargedPositionCell_disjoint c.r x c.positive hkl)
    hk.1.2 hl.1.2

/-- The extended masses sum to the entrance-supported time-bin mass. -/
theorem tsum_enlargedPositionVisitCell_measure (nu : Measure Point) (c : Clock)
    (s x : ℝ) (j : ℕ) :
    (∑' k : ℤ, nu (enlargedStartCell c s x j k ∩
      {p | p.velocity 0 ∈ closure c.entrance})) =
      nu {p | p.time ∈ enlargedTimeBin c.r s j ∧
        p.velocity 0 ∈ closure c.entrance} := by
  rw [← measure_iUnion (pairwiseDisjoint_enlargedPositionVisitCell c s x j)
    (measurableSet_enlargedPositionVisitCell c s x j)]
  rw [iUnion_enlargedPositionVisitCell]

/-- The real position masses sum exactly to the real time count for finite measures. -/
theorem enlargedPositionVisitMass_sum (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) :
    (∑' k : ℤ, enlargedPositionVisitMass nu c s x j k) =
      enlargedTimeVisitMass nu c s j := by
  unfold enlargedPositionVisitMass enlargedTimeVisitMass
  rw [← ENNReal.tsum_toReal_eq]
  · rw [tsum_enlargedPositionVisitCell_measure]
  · intro k
    exact measure_ne_top nu _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
