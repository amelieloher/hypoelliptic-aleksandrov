module

public import PDEFoundation.Measure.Jensen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Jensen's inequality on the unit interval

The Lebesgue measure of `[0,1]` is one, so restricting volume to that
interval is a probability measure.  This file packages the resulting
real-power Jensen inequality in interval-integral notation.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- The `p`th power of an integral on `[0,1]` is controlled by the integral of
the `p`th power, for every real `p ≥ 1`. -/
theorem abs_intervalIntegral_rpow_le_intervalIntegral_abs_rpow
    {f : ℝ → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : IntervalIntegrable f volume 0 1)
    (hfp : IntervalIntegrable (fun t => |f t| ^ p)
      volume 0 1) :
    |∫ t in (0 : ℝ)..1, f t| ^ p ≤
      ∫ t in (0 : ℝ)..1, |f t| ^ p := by
  let μ : Measure ℝ :=
    volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simp only [μ, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hfμ : Integrable f μ := by
    change
      Integrable f
        (volume.restrict (Icc (0 : ℝ) 1))
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).mp hf
  have hfpμ :
      Integrable (fun t => |f t| ^ p) μ := by
    change
      Integrable (fun t => |f t| ^ p)
        (volume.restrict (Icc (0 : ℝ) 1))
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).mp hfp
  have hJensen :=
    abs_integral_rpow_le_integral_abs_rpow
      (μ := μ) hp hfμ hfpμ
  simpa only [μ, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one] using
      hJensen

end PDE
