module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
import Mathlib.Tactic

/-! # Exact exponent arithmetic in the below-four band estimate -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The source band exponent is exactly the homogeneity minus the visit-sum exponent. -/
theorem coreStartBand_exponent (alpha q : ℝ) :
    (6 - 4 * q) - (1 - (2 - alpha) * (q - 1)) =
      4 - 3 * q + (1 - alpha) * (q - 1) := by ring

/-- The visit-sum factor converts to the exact relative-radius power, uniformly up to `6R`. -/
theorem coreStartBand_scaling (r R a eta : ℝ) (hr : 0 < r) (hR : 0 < R)
    (heta : 0 ≤ eta) (hscale : r ≤ 6 * R) :
    r ^ a * (1 + R / r) ^ eta ≤
      7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
  have hu : 0 < r / R := div_pos hr hR
  have hbase : 1 + R / r ≤ 7 * (R / r) := by
    have h : 1 ≤ 6 * (R / r) := by
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hr).2 (by simpa only [one_mul] using hscale)
    linarith
  have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + R / r) hbase heta
  have heq : r ^ a * (7 * (R / r)) ^ eta =
      7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
    have hrrep : r = R * (r / R) := by field_simp
    have hinv : R / r = (r / R)⁻¹ := by field_simp
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (by positivity), hinv,
      Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
    nth_rw 1 [hrrep]
    rw [Real.mul_rpow hR.le hu.le]
    calc
      _ = 7 ^ eta * R ^ a * ((r / R) ^ a * (r / R) ^ (-eta)) := by ring
      _ = 7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
        rw [← Real.rpow_add hu]
        simp only [sub_eq_add_neg]

  exact (mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hr.le a)).trans_eq heq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
