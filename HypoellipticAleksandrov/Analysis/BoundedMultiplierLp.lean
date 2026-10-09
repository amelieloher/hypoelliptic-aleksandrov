module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Bounded measurable scalar multiplier on `Lᵖ`

This module records the generic `Lᵖ` membership and real-valued seminorm estimate for
multiplication by an almost-everywhere bounded measurable scalar function.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Analysis

open MeasureTheory
open scoped ENNReal

/-- Multiplication by an almost-everywhere bounded measurable scalar preserves
`Lᵖ` and obeys the corresponding real-valued seminorm estimate. -/
theorem memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      ENNReal.toReal (eLpNorm (fun x => a x * f x) p μ) ≤
        M * ENNReal.toReal (eLpNorm f p μ) := by
  have hmeas : AEStronglyMeasurable (fun x => a x * f x) μ := ha.mul hf.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, ‖a x * f x‖ ≤ M * ‖f x‖ := by
    filter_upwards [haM] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul hx le_rfl (abs_nonneg (f x)) hM
  have haf : MemLp (fun x => a x * f x) p μ := MemLp.of_le_mul hf hmeas hpoint
  have hle : eLpNorm (fun x => a x * f x) p μ ≤
      ENNReal.ofReal M * eLpNorm f p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint p
  refine ⟨haf, ?_⟩
  have htop : ENNReal.ofReal M * eLpNorm f p μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hr

end HypoellipticAleksandrov.Analysis
