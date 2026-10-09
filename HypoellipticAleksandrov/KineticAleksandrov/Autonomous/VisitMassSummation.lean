module

public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Passing uniform finite partial counting bounds to the full counting measure -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- A uniform mass bound on finite partial sums bounds the full positive measure sum. -/
theorem visit_sum_mass_le_of_partial_mass_le {X : Type*} [MeasurableSpace X]
    (mu : ℕ → Measure X) (C : ℝ≥0∞)
    (hC : ∀ N, (∑ n ∈ Finset.range N, mu n) univ ≤ C) :
    Measure.sum mu univ ≤ C := by
  rw [Measure.sum_apply _ MeasurableSet.univ]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  simpa only [Measure.finsetSum_apply, MeasurableSet.univ] using hC N

/-- A finite uniform partial counting bound proves that the full count is a finite measure. -/
theorem visit_sum_isFiniteMeasure_of_partial_mass_le {X : Type*} [MeasurableSpace X]
    (mu : ℕ → Measure X) (C : ℝ≥0∞) (hCfinite : C < ⊤)
    (hC : ∀ N, (∑ n ∈ Finset.range N, mu n) univ ≤ C) :
    IsFiniteMeasure (Measure.sum mu) :=
  ⟨(visit_sum_mass_le_of_partial_mass_le mu C hC).trans_lt hCfinite⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
