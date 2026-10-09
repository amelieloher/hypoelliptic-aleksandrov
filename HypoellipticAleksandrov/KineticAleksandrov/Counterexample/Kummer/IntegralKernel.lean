module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Positive Laplace kernels for the Kummer integral

This module develops the kernel on real parameters, independently of the series module.
Only positive integration variables and positive Laplace parameters are characterized.
-/

@[expose] public section

open Set MeasureTheory Real

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Literal real Laplace kernel, before bundling the positive first parameter. -/
noncomputable def laplaceKernelReal (a b z t : ℝ) : ℝ :=
  Real.exp (-(z * t)) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)

/-- The kernel is strictly positive on the integration domain. -/
theorem laplaceKernelReal_pos (a b z t : ℝ) (ht : 0 < t) :
    0 < laplaceKernelReal a b z t := by
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _))
    (Real.rpow_pos_of_pos (by linarith only [ht]) _)

/-- Continuity in the integration variable away from its endpoint. -/
theorem continuousOn_laplaceKernelReal (a b z : ℝ) :
    ContinuousOn (laplaceKernelReal a b z) (Ioi 0) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact (continuous_const.mul continuous_id).neg.rexp.continuousOn
    · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  · exact (continuousOn_const.add continuousOn_id).rpow_const
      (fun t ht => Or.inl (by
        change 1 + t ≠ 0
        exact ne_of_gt (add_pos zero_lt_one ht)))

/-- A polynomial bound for the translated power on the positive half-line. -/
theorem one_add_rpow_le_polynomial (q : ℝ) (n : ℕ) (hqn : q ≤ (n : ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ q ≤ (2 : ℝ) ^ n * (1 + t ^ n) := by
  have hbase : 1 ≤ 1 + t := by linarith only [ht]
  have hpow : (1 + t) ^ q ≤ (1 + t) ^ n := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hqn
  apply hpow.trans
  by_cases ht1 : t ≤ 1
  · have hsmall : (1 + t) ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [ht1]) n
    exact hsmall.trans (le_mul_of_one_le_right (by positivity) (by
      have := pow_nonneg ht n
      linarith only [this]))
  · have ht1' : 1 ≤ t := (lt_of_not_ge ht1).le
    have hlarge : (1 + t) ^ n ≤ (2 * t) ^ n :=
      pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [ht1']) n
    rw [mul_pow] at hlarge
    exact hlarge.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- The scaled Gamma kernel is integrable for every positive shape and rate. -/
theorem integrableOn_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a - 1))
      (Ioi 0) volume := by
  have hscaled : IntegrableOn
      (fun t : ℝ => Real.exp (-(z * t)) * (z * t) ^ (a - 1))
      (Ioi 0) volume := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) 0 hz).mpr
    simpa only [mul_zero] using Real.GammaIntegral_convergent ha
  have h := hscaled.const_mul (z ^ (a - 1))⁻¹
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  change (z ^ (a - 1))⁻¹ *
    (Real.exp (-(z * t)) * (z * t) ^ (a - 1)) =
      Real.exp (-(z * t)) * t ^ (a - 1)
  rw [Real.mul_rpow hz.le ht.le]
  have hn := (Real.rpow_pos_of_pos hz (a - 1)).ne'
  field_simp

/-- Absolute convergence of the full Kummer Laplace kernel. -/
theorem integrableOn_laplaceKernelReal (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (laplaceKernelReal a b z) (Ioi 0) volume := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b - a - 1)
  have hnshape : 0 < a + (n : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
  have hdom := ((integrableOn_gammaKernel a z ha hz).add
    (integrableOn_gammaKernel (a + n) z hnshape hz)).const_mul ((2 : ℝ) ^ n)
  apply hdom.mono'
  · exact (continuousOn_laplaceKernelReal a b z).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (laplaceKernelReal_pos a b z t ht)]
    have hp := one_add_rpow_le_polynomial (b - a - 1) n hn.le t ht.le
    have hmul := mul_le_mul_of_nonneg_left hp
      (mul_pos (Real.exp_pos (-(z * t))) (Real.rpow_pos_of_pos ht (a - 1))).le
    have heq : t ^ (a + (n : ℝ) - 1) = t ^ (a - 1) * t ^ n := by
      rw [show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring,
        Real.rpow_add ht, Real.rpow_natCast]
    change laplaceKernelReal a b z t ≤
      2 ^ n * (Real.exp (-(z * t)) * t ^ (a - 1) +
        Real.exp (-(z * t)) * t ^ (a + (n : ℝ) - 1))
    rw [heq]
    exact hmul.trans_eq (by ring)

/-- The integral of the kernel is strictly positive. -/
theorem integral_laplaceKernelReal_pos (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    0 < ∫ t in Ioi (0 : ℝ), laplaceKernelReal a b z t := by
  have hs : Function.support (laplaceKernelReal a b z) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro t ht
    exact (laplaceKernelReal_pos a b z t ht).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (laplaceKernelReal_pos a b z t ht).le
  · exact integrableOn_laplaceKernelReal a b z ha hz

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
