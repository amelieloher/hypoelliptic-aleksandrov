module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapNorm
import Mathlib.Tactic

/-! # Holder control of a finite positive mixture with a uniform Lq bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory
open scoped ENNReal

/-- Holder bounds the q-power of a finite positive integral by its mass and power integral. -/
theorem position_integral_rpow_le {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) (q : ℝ) (hq : 1 < q) :
    (∫⁻ x, f x ∂nu) ^ q ≤ (nu Set.univ) ^ (q - 1) * ∫⁻ x, f x ^ q ∂nu := by
  have hc : q.HolderConjugate (q / (q - 1)) := Real.holderConjugate_iff.mpr
    ⟨hq, by field_simp; ring⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq nu hc hf.aemeasurable
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  have he : q / (q / (q - 1)) = q - 1 := by
    field_simp
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul] at h
  apply (ENNReal.rpow_le_rpow h (by linarith)).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul,
    one_div_mul_cancel (by linarith : q ≠ 0), ENNReal.rpow_one,
    ← ENNReal.rpow_mul, div_mul_eq_mul_div, one_mul, he, mul_comm]

/-- Positive powers combine with one additional factor, including zero and infinity. -/
theorem position_rpow_sub_one_mul (x : ℝ≥0∞) (q : ℝ) (hq : 1 ≤ q) :
    x ^ (q - 1) * x = x ^ q := by
  calc
    _ = x ^ (q - 1) * x ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
    _ = x ^ ((q - 1) + 1) :=
      (ENNReal.rpow_add_of_nonneg (q - 1) 1 (by linarith) (by norm_num)).symm
    _ = x ^ q := by rw [sub_add_cancel]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
