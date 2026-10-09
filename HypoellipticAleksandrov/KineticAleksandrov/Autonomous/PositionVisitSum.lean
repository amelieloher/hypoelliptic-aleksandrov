module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionPowerSum
import Mathlib.Tactic

/-! # The largest-cell times total-mass step in position visit summation -/

public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A nonnegative bounded mass obeys the source largest-cell power inequality. -/
theorem position_mass_rpow_le {x M q : ℝ} (hx : 0 ≤ x) (hM : x ≤ M) (hq : 1 < q) :
    x ^ q ≤ M ^ (q - 1) * x := by
  calc
    x ^ q = x ^ (q - 1) * x := by
      calc
        _ = x ^ ((q - 1) + 1) := by congr 1; ring
        _ = _ := by
          rw [Real.rpow_add_of_nonneg hx (by linarith : 0 ≤ q - 1) zero_le_one,
            Real.rpow_one]
    _ ≤ M ^ (q - 1) * x := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx hM (by linarith)) hx

/-- Extended real masses of all position cells sum to the time-bin mass. -/
theorem tsum_ofReal_enlargedPositionVisitMass (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) :
    (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k)) =
      ENNReal.ofReal (enlargedTimeVisitMass nu c s j) := by
  unfold enlargedPositionVisitMass enlargedTimeVisitMass
  simp_rw [ENNReal.ofReal_toReal (measure_ne_top nu _)]
  exact tsum_enlargedPositionVisitCell_measure nu c s x j

/-- For each time bin, the q-power sum is largest-cell power times total mass. -/
theorem enlargedPositionVisitMass_power_sum_le (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) (M q : ℝ) (hM : 0 ≤ M) (hq : 1 < q)
    (hcell : ∀ k : ℤ, enlargedPositionVisitMass nu c s x j k ≤ M) :
    (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
      ENNReal.ofReal (M ^ (q - 1) * enlargedTimeVisitMass nu c s j) := by
  have hn : ∀ k : ℤ, 0 ≤ enlargedPositionVisitMass nu c s x j k :=
    fun _ => ENNReal.toReal_nonneg
  calc
    _ ≤ ∑' k : ℤ, ENNReal.ofReal
        (M ^ (q - 1) * enlargedPositionVisitMass nu c s x j k) :=
      ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal
        (position_mass_rpow_le (hn k) (hcell k) hq)
    _ = ENNReal.ofReal (M ^ (q - 1)) *
        ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k) := by
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [tsum_ofReal_enlargedPositionVisitMass,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]

/-- Combining the two decay estimates gives the literal exponent used in the time sum. -/
theorem enlargedPositionVisitMass_power_sum_decay_le
    (nu : Measure Point) [IsFiniteMeasure nu] (c : Clock) (s x : ℝ) (j : ℕ)
    (Ct Cp g q : ℝ) (_hCt : 0 ≤ Ct) (hCp : 0 ≤ Cp) (hq : 1 < q)
    (htime : enlargedTimeVisitMass nu c s j ≤ Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hcell : ∀ k : ℤ,
      enlargedPositionVisitMass nu c s x j k ≤ Cp * (1 + (j : ℝ)) ^ (-g / 2)) :
    (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
      ENNReal.ofReal (Cp ^ (q - 1) * Ct *
        (1 + (j : ℝ)) ^ (-(1 + g * (q - 1)) / 2)) := by
  have hp : 0 < 1 + (j : ℝ) := by positivity
  apply (enlargedPositionVisitMass_power_sum_le nu c s x j
    (Cp * (1 + (j : ℝ)) ^ (-g / 2)) q
      (mul_nonneg hCp (Real.rpow_nonneg hp.le _)) hq hcell).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left htime
    (Real.rpow_nonneg (mul_nonneg hCp (Real.rpow_nonneg hp.le (-g / 2))) (q - 1))
  apply h.trans_eq
  rw [Real.mul_rpow hCp (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le]
  calc
    _ = Cp ^ (q - 1) * Ct *
        ((1 + (j : ℝ)) ^ ((-g / 2) * (q - 1)) *
          (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hp]
      congr 2
      ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
