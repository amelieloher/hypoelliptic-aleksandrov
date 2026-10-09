module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon
import Mathlib.Tactic

/-! # Identifying a truncated time bin with its source start-count slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The source position-resolved start count on an elapsed half-open time slab. -/
def enlargedPositionSlabMass (nu : Measure Point) (c : Clock) (s x a b : ℝ) (k : ℤ) : ℝ :=
  (nu {p | s + a < p.time ∧ p.time ≤ s + b ∧
    p.position 0 ∈ enlargedPositionCell c.r x k ∧
      p.velocity 0 ∈ closure c.entrance}).toReal

/-- A noninitial cell is precisely its slab truncated at the observation horizon. -/
theorem enlargedPositionVisitMass_eq_truncated_slab
    (nu : Measure Point) (c : Clock) (s x T : ℝ) (j : ℕ) (k : ℤ)
    (hj : j ≠ 0) (hs : ∀ᵐ p ∂nu, p.time < s + T) :
    enlargedPositionVisitMass nu c s x j k =
      enlargedPositionSlabMass nu c s x ((j : ℝ) * c.r ^ 2)
        (min (((j : ℝ) + 1) * c.r ^ 2) T) k := by
  unfold enlargedPositionVisitMass enlargedPositionSlabMass
  congr 1
  apply measure_congr
  filter_upwards [hs] with p hp
  apply propext
  simp only [mem_inter_iff, enlargedStartCell, enlargedTimeBin, hj, ite_false,
    mem_ofPred_eq, mem_Ioc]
  have he : s + min (((j : ℝ) + 1) * c.r ^ 2) T =
      min (s + ((j : ℝ) + 1) * c.r ^ 2) (s + T) := (min_add_add_left s _ _).symm
  rw [he, le_min_iff]
  have hple := hp.le
  tauto

/-- Each cell mass is bounded by its time-bin count for any finite measure. -/
theorem enlargedPositionVisitMass_le_timeVisitMass (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) (k : ℤ) :
    enlargedPositionVisitMass nu c s x j k ≤ enlargedTimeVisitMass nu c s j := by
  apply ENNReal.toReal_mono (measure_ne_top nu _)
  apply measure_mono
  intro p hp
  exact ⟨hp.1.1, hp.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
