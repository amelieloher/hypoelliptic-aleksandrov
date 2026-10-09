module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailMoments
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
import Mathlib.Tactic

/-! # Moment inequalities on both sides of zero -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The oriented first moment stays nonnegative on the negative half-line. -/
theorem bellmanAngularFirstMoment_nonneg_negative {f : ℝ → ℝ}
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) {y : ℝ} (hy : y ≤ 0) :
    0 ≤ bellmanAngularFirstMoment f y := by
  rw [bellmanAngularFirstMoment, intervalIntegral.integral_of_ge hy]
  apply neg_nonneg.mpr
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hf] with z hz hfz
  exact mul_nonpos_of_nonpos_of_nonneg hz.2 hfz

/-- The oriented second moment is nonpositive on the negative half-line. -/
theorem bellmanAngularSecondMoment_nonpos_negative {f : ℝ → ℝ}
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) {y : ℝ} (hy : y ≤ 0) :
    bellmanAngularSecondMoment f y ≤ 0 := by
  rw [bellmanAngularSecondMoment, intervalIntegral.integral_symm]
  apply neg_nonpos.mpr
  apply intervalIntegral.integral_nonneg_of_ae hy
  filter_upwards [hf] with z hz
  exact mul_nonneg (sq_nonneg z) hz

/-- On the negative side minus the second moment is bounded by minus y times the first moment. -/
theorem bellmanAngularSecondMoment_negative_bound {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : y ≤ 0) :
    -bellmanAngularSecondMoment f y ≤ -y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    intervalIntegral.integral_symm (a := y) (b := 0),
    intervalIntegral.integral_symm (a := y) (b := 0), neg_neg]
  have he : -y * (-(∫ z in y..0, z * f z)) = ∫ z in y..0, y * (z * f z) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [he]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume y 0 := by
    simpa only [pow_one] using bellmanAngularMoment_intervalIntegrable hi y 0 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi y 0 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.1) (mul_nonneg (neg_nonneg.mpr hzy.2) hz)]

/-- The second moment divided by its endpoint is bounded in norm by the first moment. -/
theorem bellmanAngularSecondMoment_div_norm_le {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (y : ℝ) :
    ‖bellmanAngularSecondMoment f y / y‖ ≤ bellmanAngularFirstMoment f y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hm := bellmanAngularSecondMoment_nonpos_negative hf hy.le
    have hb := bellmanAngularSecondMoment_negative_bound hi hf hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg_of_nonpos hm hy.le)]
    apply (div_le_iff_of_neg hy).mpr
    linarith
  · subst y
    simp only [div_zero, norm_zero, bellmanAngularFirstMoment, intervalIntegral.integral_same]
    exact le_rfl
  · have hm := bellmanAngularSecondMoment_nonneg hf hy.le
    have hb := bellmanAngularSecondMoment_le hi hf hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm hy.le)]
    exact (div_le_iff₀ hy).mpr (by simpa only [mul_comm] using hb)

end HypoellipticAleksandrov.KineticAleksandrov
