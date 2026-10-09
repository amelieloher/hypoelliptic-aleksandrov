module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapHolder
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The two-index positive Young inequality

Apply this with the additive group `ℤ × ℤ` and the exponential finite-speed
kernel. The counting measure proof retains infinite sums throughout.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- Weighted positive sums satisfy the q-power form of Holder's inequality. -/
theorem position_weighted_tsum_rpow_le {ι : Type*} [Countable ι]
    (w a : ι → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' i, w i * a i) ^ q ≤ (∑' i, w i) ^ (q - 1) * ∑' i, w i * a i ^ q := by
  let : MeasurableSpace ι := ⊤
  have hm (f : ι → ℝ≥0∞) : Measurable f := measurable_from_top
  have h := position_integral_rpow_le (Measure.count.withDensity w) a (hm a) q hq
  have hw : (Measure.count.withDensity w) univ = ∑' i, w i := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
  rw [hw, lintegral_withDensity_eq_lintegral_mul _ (hm w) (hm a),
    lintegral_withDensity_eq_lintegral_mul _ (hm w) ((hm a).pow_const q),
    lintegral_count, lintegral_count] at h
  exact h

/-- Translation-invariant positive convolution is bounded on the q-power counting norm. -/
theorem position_two_index_young {ι : Type*} [AddCommGroup ι] [Countable ι]
    (w a : ι → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' g, (∑' h, w h * a (g - h)) ^ q) ≤
      (∑' h, w h) ^ q * ∑' g, a g ^ q := by
  calc
    _ ≤ ∑' g, (∑' h, w h) ^ (q - 1) * ∑' h, w h * a (g - h) ^ q :=
      ENNReal.tsum_le_tsum (fun g => position_weighted_tsum_rpow_le w
        (fun h => a (g - h)) q hq)
    _ = (∑' h, w h) ^ (q - 1) * ∑' h, w h * ∑' g, a (g - h) ^ q := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
      congr 1
      apply tsum_congr
      intro h
      exact ENNReal.tsum_mul_left
    _ = (∑' h, w h) ^ (q - 1) * ((∑' h, w h) * ∑' g, a g ^ q) := by
      have hshift (h : ι) : (∑' g, a (g - h) ^ q) = ∑' g, a g ^ q := by
        exact (Equiv.subRight h).tsum_eq (fun g => a g ^ q)
      simp_rw [hshift]
      rw [ENNReal.tsum_mul_right]
    _ = (∑' h, w h) ^ q * ∑' g, a g ^ q := by
      rw [← mul_assoc, position_rpow_sub_one_mul _ q hq.le]


end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
