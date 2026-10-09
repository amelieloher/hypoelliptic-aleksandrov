module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursion
import Mathlib.Tactic

/-! # Positive measure telescoping for a finite number of visits -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

/-- Finite telescoping retains the genuine continuation measure after the last visit. -/
theorem alternating_measure_telescope (total initial : Measure Point)
    (charge remainder : ℕ → Measure Point)
    (hzero : total = initial + remainder 0)
    (hstep : ∀ n, remainder n = charge n + remainder (n + 1)) (N : ℕ) :
    total = initial + ∑ n ∈ Finset.range N, charge n + remainder N := by
  induction N with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hzero
  | succ N ih =>
    calc
      total = initial + ∑ n ∈ Finset.range N, charge n + remainder N := ih
      _ = initial + ∑ n ∈ Finset.range (N + 1), charge n + remainder (N + 1) := by
        rw [hstep N, Finset.sum_range_succ]
        ac_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
