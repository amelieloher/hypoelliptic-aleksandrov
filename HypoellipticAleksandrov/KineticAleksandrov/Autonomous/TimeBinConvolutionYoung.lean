module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumKernel

/-! # Young's inequality for the literal one-index time convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal Classical

/-- Source-index convolution obeys Young's q-power counting estimate on the integer grid. -/
theorem entrance_time_young (w a : ℤ → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' j : ℤ, (∑' k : ℤ, w (j - k) * a k) ^ q) ≤
      (∑' k : ℤ, w k) ^ q * ∑' j : ℤ, a j ^ q := by
  have he (j : ℤ) : (∑' k : ℤ, w (j - k) * a k) =
      ∑' k : ℤ, w k * a (j - k) := by
    have h := (Equiv.subLeft j).tsum_eq (fun k => w (j - k) * a k)
    simpa only [Equiv.subLeft_apply, sub_sub_cancel] using h.symm
  simp_rw [he]
  exact position_two_index_young w a q hq

/-- Exponential time-bin weights have a summable integer majorant. -/
theorem entranceBinWeight_le (c₀ : ℝ) (hc₀ : 0 < c₀) (j k : ℤ) :
    entranceBinWeight c₀ j k ≤ ENNReal.ofReal (Real.exp c₀) *
      ENNReal.ofReal (Real.exp (-c₀ * |((j - k : ℤ) : ℝ)|)) := by
  unfold entranceBinWeight
  split_ifs with hkj
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ (j : ℝ) - (k : ℝ) := by exact_mod_cast sub_nonneg.mpr hkj
    rw [Int.cast_sub, abs_of_nonneg hh]
    have hm := le_max_left ((j : ℝ) - (k : ℝ) - 1) 0
    change -c₀ * max ((j : ℝ) - (k : ℝ) - 1) 0 ≤ _
    nlinarith only [hc₀, hm]
  · exact zero_le

/-- The actual causal time convolution has its q-power sum bounded by the input mass sum. -/
theorem entrance_convolution_power_sum (c₀ : ℝ) (hc₀ : 0 < c₀)
    (a : ℤ → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' j : ℤ, (∑' k : ℤ, entranceBinWeight c₀ j k * a k) ^ q) ≤
      (ENNReal.ofReal (Real.exp c₀) *
        ∑' k : ℤ, ENNReal.ofReal (Real.exp (-c₀ * |(k : ℝ)|))) ^ q *
          ∑' k : ℤ, a k ^ q := by
  let D := ENNReal.ofReal (Real.exp c₀)
  let w := fun k : ℤ => ENNReal.ofReal (Real.exp (-c₀ * |(k : ℝ)|))
  have hc (j : ℤ) : (∑' k : ℤ, entranceBinWeight c₀ j k * a k) ≤
      D * ∑' k : ℤ, w (j - k) * a k := by
    calc
      _ ≤ ∑' k : ℤ, D * w (j - k) * a k := by
        apply ENNReal.tsum_le_tsum
        intro k
        gcongr
        exact entranceBinWeight_le c₀ hc₀ j k
      _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' j : ℤ, (D * ∑' k : ℤ, w (j - k) * a k) ^ q :=
      ENNReal.tsum_le_tsum (fun j => ENNReal.rpow_le_rpow (hc j) (by linarith))
    _ = D ^ q * ∑' j : ℤ, (∑' k : ℤ, w (j - k) * a k) ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
      rw [ENNReal.tsum_mul_left]
    _ ≤ D ^ q * ((∑' k : ℤ, w k) ^ q * ∑' k : ℤ, a k ^ q) := by
      gcongr
      exact entrance_time_young w a q hq
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
