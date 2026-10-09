module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Passing compact smooth source bounds to total occupation mass -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- Inner regularity transfers a uniform bound on smooth compact unit tests to mass. -/
theorem measure_mass_le_of_smooth_unit_tests {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SigmaCompactSpace E]
    (mu : Measure E) [IsFiniteMeasure mu] {U : Set E} (hU : IsOpen U)
    (hs : mu.restrict U = mu) (C : ℝ)
    (h : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x ∧ f x ≤ 1) → ∫ x, f x ∂mu ≤ C) :
    mu univ ≤ ENNReal.ofReal C := by
  have he : mu univ = mu U := by
    conv_lhs => rw [← hs]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [he, hU.measure_eq_iSup_isCompact mu]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  obtain ⟨f, hfs, hfc, hfU, hf01, hfK⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK hU hKU
  have hi : Integrable f mu := hfs.continuous.integrable_of_hasCompactSupport hfc
  calc
    mu K = ∫⁻ x, K.indicator 1 x ∂mu := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · simp [indicator_of_mem hx, hfK x hx]
      · simp [indicator_of_notMem hx]
    _ = ENNReal.ofReal (∫ x, f x ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun x => (hf01 x).1))).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (h f hfs hfc hfU hf01)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
