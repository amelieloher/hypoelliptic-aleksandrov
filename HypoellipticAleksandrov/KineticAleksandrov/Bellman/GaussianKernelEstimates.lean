module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernel
import Mathlib.Tactic

/-! # Elementary estimates for the time-integrated Gaussian away from its pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A uniform quadratic lower bound for the Gaussian precision at small positive time. -/
theorem bellmanGaussianExponent_le_smallTime (t : BellmanPositiveTime) (ht : t.val ≤ 1)
    (q : ℝ × ℝ) :
    bellmanGaussianExponent t q ≤ -(q.1 ^ 2 + q.2 ^ 2) / (8 * t.val) := by
  have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
  have hcoeff : 0 ≤ 24 - 7 * t.val ^ 2 := by linarith only [ht2]
  have hQ : 0 ≤ (24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
      7 * t.val ^ 2 * q.2 ^ 2 := by
    nlinarith only [sq_nonneg (12 * q.1 - 7 * t.val * q.2),
      mul_nonneg hcoeff (sq_nonneg q.1)]
  have hidentity : bellmanGaussianExponent t q +
      (q.1 ^ 2 + q.2 ^ 2) / (8 * t.val) =
      -((24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
        7 * t.val ^ 2 * q.2 ^ 2) / (8 * t.val ^ 3) := by
    dsimp [bellmanGaussianExponent]
    field_simp
    ring
  have hneg : -((24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
      7 * t.val ^ 2 * q.2 ^ 2) / (8 * t.val ^ 3) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hQ)
      (mul_nonneg (by norm_num) (pow_nonneg t.property.le 3))
  rw [← hidentity] at hneg
  rw [neg_div]
  linarith only [hneg]

/-- Exponential decay dominates the quadratic inverse-power singularity. -/
theorem bellman_exp_neg_le_inv_sq (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-y)).le
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hexp] at hm
  norm_num at hm
  apply (le_div_iff₀ (pow_pos hy 2)).mpr
  nlinarith only [hm]

/-- At small time the kernel is uniformly bounded on each plane set away from the origin. -/
theorem bellmanGaussianKernel_le_smallTime (t : BellmanPositiveTime) (ht : t.val ≤ 1)
    (q : ℝ × ℝ) (a : ℝ) (ha : 0 < a) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) :
    bellmanGaussianKernel t q ≤ 64 * Real.sqrt 3 / (Real.pi * a ^ 2) := by
  have hE : bellmanGaussianExponent t q ≤ -a / (8 * t.val) := by
    refine (bellmanGaussianExponent_le_smallTime t ht q).trans ?_
    exact div_le_div_of_nonneg_right (neg_le_neg hq)
      (mul_nonneg (by norm_num) t.property.le)
  have he : Real.exp (bellmanGaussianExponent t q) ≤
      2 / (a / (8 * t.val)) ^ 2 := by
    refine (Real.exp_le_exp.mpr hE).trans ?_
    rw [neg_div] at *
    exact bellman_exp_neg_le_inv_sq _
      (div_pos ha (mul_pos (by norm_num) t.property))
  have hc : 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hm := mul_le_mul_of_nonneg_left he hc
  unfold bellmanGaussianKernel
  refine hm.trans_eq ?_
  field_simp [ne_of_gt t.property]
  norm_num

end HypoellipticAleksandrov.KineticAleksandrov
