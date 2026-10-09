module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
import Mathlib.Tactic

/-! # Summable powers in the preliminary entrance estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The sixth-fifths power of the core estimate has a summable positive scale power. -/
theorem preliminary_core_power_le (C R r : ℝ) (hC : 0 < C) (hR : 0 < R)
    (hr : 0 < r) (hrR : r ≤ 6 * R) :
    (C * r * (1 + R / r) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) ≤
      7 * C ^ (6 / 5 : ℝ) * R ^ (6 / 5 : ℝ) * (r / R) ^ (1 / 5 : ℝ) := by
  have hnon : 0 ≤ 1 + R / r := by positivity
  have he : (C * r * (1 + R / r) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) =
      C ^ (6 / 5 : ℝ) * (r ^ (1 / 5 : ℝ) * (r + R)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hC.le hr.le, ← Real.rpow_mul hnon]
    norm_num
    have hx : r ^ (6 / 5 : ℝ) = r ^ (1 / 5 : ℝ) * r := by
      calc
        _ = r ^ ((1 / 5 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
    rw [hx]
    field_simp
  have he' : 7 * C ^ (6 / 5 : ℝ) * R ^ (6 / 5 : ℝ) *
      (r / R) ^ (1 / 5 : ℝ) =
      C ^ (6 / 5 : ℝ) * r ^ (1 / 5 : ℝ) * (7 * R) := by
    rw [Real.div_rpow hr.le hR.le]
    have hx : R ^ (6 / 5 : ℝ) = R ^ (1 / 5 : ℝ) * R := by
      calc
        _ = R ^ ((1 / 5 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hR, Real.rpow_one]
    rw [hx]
    field_simp
  rw [he, he']
  have hp : 0 ≤ C ^ (6 / 5 : ℝ) * r ^ (1 / 5 : ℝ) := by positivity
  have hh : r + R ≤ 7 * R := by linarith only [hrR]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hp

/-- A real norm bound also bounds its positive power integral. -/
theorem preliminary_density_power_le {X : Type*} [MeasurableSpace X]
    (m : MeasureTheory.Measure X) (f : X → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal q) m)
    (hn : (MeasureTheory.eLpNorm f (ENNReal.ofReal q) m).toReal ≤ K) :
    (∫⁻ x, ‖f x‖ₑ ^ q ∂m) ≤ ENNReal.ofReal (K ^ q) := by
  apply density_power_integral_le m f q (K ^ q) hq (by positivity) hf
  rw [← Real.rpow_mul hK, mul_one_div_cancel hq.ne', Real.rpow_one]
  exact hn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
