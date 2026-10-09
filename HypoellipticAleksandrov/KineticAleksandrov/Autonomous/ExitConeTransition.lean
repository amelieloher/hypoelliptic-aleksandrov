module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # A bounded smooth increasing cone probe with positive derivative on the positive axis -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Real

/-- The source's cone probe has a uniform unit bound. -/
theorem reconstructionConeTransition_bound (x : ℝ) :
    0 ≤ expNegInvGlue x ∧ expNegInvGlue x ≤ 1 := by
  refine ⟨expNegInvGlue.nonneg x, ?_⟩
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact zero_le_one
  · rw [expNegInvGlue, ite_eq_right hx]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (not_le.mp hx).le))

/-- The exact derivative of the cone transition. -/
theorem reconstructionConeTransition_deriv (x : ℝ) :
    deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x := by
  have hh := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x).deriv
  simpa using hh

/-- The derivative is bounded and strictly positive exactly on the positive axis. -/
theorem reconstructionConeTransition_deriv_bounds (x : ℝ) :
    0 ≤ deriv expNegInvGlue x ∧ deriv expNegInvGlue x ≤ 2 ∧
      (0 < x → 0 < deriv expNegInvGlue x) := by
  rw [reconstructionConeTransition_deriv]
  refine ⟨mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg x), ?_, ?_⟩
  · by_cases hx : x ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
      norm_num
    · have hx' : 0 < x := not_le.mp hx
      have hh := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx').le 2
      norm_num only [Nat.factorial, Nat.cast_ofNat] at hh
      have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x⁻¹)).le
      rw [expNegInvGlue, ite_eq_right hx]
      have he : Real.exp x⁻¹ * Real.exp (-x⁻¹) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith
  · intro hx
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr hx)) (expNegInvGlue.pos_of_pos hx)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
