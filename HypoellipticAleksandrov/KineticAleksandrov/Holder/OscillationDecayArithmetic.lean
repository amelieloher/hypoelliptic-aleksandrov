module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! # The source logarithmic exponent and the geometric-to-power interpolation -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The literal source exponent is positive, at most one, and absorbs the contraction. -/
theorem source_holder_exponent {theta q : ℝ} (ht : 0 < theta) (ht1 : theta < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    let alpha := min 1 (Real.log (1 / q) / Real.log (1 / theta))
    0 < alpha ∧ alpha ≤ 1 ∧ q ≤ theta ^ alpha := by
  have hlt : Real.log theta < 0 := Real.log_neg ht ht1
  have hlq : Real.log q < 0 := Real.log_neg hq hq1
  have hratio : Real.log (1 / q) / Real.log (1 / theta) =
      Real.log q / Real.log theta := by rw [one_div, one_div, Real.log_inv, Real.log_inv]; ring
  dsimp only
  rw [hratio]
  refine ⟨lt_min zero_lt_one (div_pos_of_neg_of_neg hlq hlt), min_le_left _ _, ?_⟩
  apply (Real.le_rpow_iff_log_le hq ht).mpr
  have he := mul_le_mul_of_nonpos_right (min_le_right (1 : ℝ)
    (Real.log q / Real.log theta)) hlt.le
  rw [div_mul_cancel₀ _ hlt.ne] at he
  exact he

/-- A geometric shell bounds the corresponding contraction by the source power multiplier. -/
theorem contraction_power_le_scale_power {theta q alpha x : ℝ}
    (ht : 0 < theta) (hq : 0 ≤ q) (ha : 0 < alpha) (hqa : q ≤ theta ^ alpha)
    (n : ℕ) (hn : theta ^ (n + 1) < x) :
    q ^ n ≤ theta ^ (-alpha) * x ^ alpha := by
  have hs : theta ^ n < x / theta := by
    rw [pow_succ] at hn
    exact (lt_div_iff₀ ht).mpr hn
  calc
    q ^ n ≤ (theta ^ alpha) ^ n := pow_le_pow_left₀ hq hqa n
    _ = (theta ^ n) ^ alpha := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
        ← Real.rpow_natCast, ← Real.rpow_mul ht.le, mul_comm alpha (n : ℝ)]
    _ ≤ (x / theta) ^ alpha := Real.rpow_le_rpow (pow_nonneg ht.le n) hs.le ha.le
    _ = theta ^ (-alpha) * x ^ alpha := by
      rw [Real.div_rpow (by linarith only [hn, pow_pos ht (n + 1)]) ht.le,
        Real.rpow_neg ht.le, div_eq_mul_inv, mul_comm]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
