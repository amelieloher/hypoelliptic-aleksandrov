module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Jensen's inequality for scalar moments

This file packages the probability-measure form of Jensen's inequality used
by the quantitative PDE development. For a real exponent `p ≥ 1`, it compares
the `p`th power of the absolute expectation with the expected `p`th absolute
power.

The proof applies Jensen's inequality to the nonnegative function `|f|` and
then uses the integral triangle inequality. Both integrability assumptions
are explicit, matching the hypotheses of Mathlib's Bochner-integral Jensen
theorem.

## Main result

- `abs_integral_rpow_le_integral_abs_rpow`: scalar moment Jensen inequality.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Jensen's inequality for the `p`th absolute moment on a probability space.

Here `^ p` is real exponentiation (`Real.rpow`). The assumption that `f` is
integrable supplies the first-moment input, while integrability of
`x ↦ |f x| ^ p` makes the right-hand Bochner integral meaningful.
-/
theorem abs_integral_rpow_le_integral_abs_rpow
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Integrable f μ)
    (hfp : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ ∫ x, |f x| ^ p ∂μ := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  have hJensen :
      (∫ x, |f x| ∂μ) ^ p ≤
        ∫ x, |f x| ^ p ∂μ := by
    simpa only [Function.comp_apply] using
      (convexOn_rpow hp).map_integral_le
        (Real.continuous_rpow_const hpNonneg).continuousOn
        isClosed_Ici
        (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
        hf.abs hfp
  exact
    (Real.rpow_le_rpow (abs_nonneg _)
      MeasureTheory.abs_integral_le_integral_abs hpNonneg).trans
        hJensen

end PDE
