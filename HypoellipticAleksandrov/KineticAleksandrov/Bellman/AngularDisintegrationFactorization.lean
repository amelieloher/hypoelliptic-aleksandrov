module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationSlices
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-! # Product factorization of a locally finite measure invariant in its first coordinate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Closed bounded intervals form finite spanning sets for a locally finite real measure. -/
theorem bellman_finiteSpanning_closedIntervals (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] :
    Nonempty (μ.FiniteSpanningSetsIn {S | ∃ a b : ℝ, a ≤ b ∧ Icc a b = S}) := by
  refine ⟨{
    set := fun n => Icc (-(n : ℝ)) (n : ℝ)
    set_mem := fun n => ⟨_, _, neg_le_self (Nat.cast_nonneg n), rfl⟩
    finite := fun _ => isCompact_Icc.measure_lt_top
    spanning := ?_ }⟩
  ext x
  simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact ⟨n, by linarith only [neg_abs_le x, hn], by linarith only [le_abs_self x, hn]⟩

/-- Radial translation invariance forces a product with the unit-radius angular section. -/
theorem bellman_translation_factorization (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ]
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ) :
    ρ = (volume : Measure ℝ).prod (bellmanUnitSection ρ) := by
  let F := bellmanUnitSection ρ
  let : IsFiniteMeasureOnCompacts F := bellmanUnitSection_finiteOnCompacts ρ
  let C : Set (Set ℝ) := {S | ∃ a b : ℝ, a ≤ b ∧ Icc a b = S}
  have hgen : MeasurableSpace.generateFrom C = (inferInstance : MeasurableSpace ℝ) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Icc ℝ)).symm
  have hpi : IsPiSystem C := isPiSystem_Icc id id
  obtain ⟨hvol⟩ := bellman_finiteSpanning_closedIntervals (volume : Measure ℝ)
  obtain ⟨hF⟩ := bellman_finiteSpanning_closedIntervals F
  apply Eq.symm
  apply Measure.prod_eq_generateFrom hgen hgen hpi hpi hvol hF
  rintro A ⟨a, b, hab, rfl⟩ B ⟨c, d, hcd, rfl⟩
  exact bellman_translation_rectangle ρ hρ measurableSet_Icc isCompact_Icc

end HypoellipticAleksandrov.KineticAleksandrov
