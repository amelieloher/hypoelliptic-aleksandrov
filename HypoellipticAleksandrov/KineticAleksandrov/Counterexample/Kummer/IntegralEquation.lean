module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralDerivatives
import Mathlib.Tactic

/-!
# The differential equation for the positive Kummer integral

Integration of the derivative of the flux gives the moment relation, with both endpoint
terms proved to vanish. The relation and differentiation under the integral yield the ODE.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- The flux whose integral derivative supplies Kummer's equation. -/
def laplaceFlux (a b z t : ℝ) : ℝ :=
  Real.exp (-(z * t)) * t ^ a * (1 + t) ^ (b - a)

/-- The flux vanishes at the lower endpoint for positive shape. -/
theorem laplaceFlux_zero (a b z : ℝ) (ha : 0 < a) : laplaceFlux a b z 0 = 0 := by
  simp only [laplaceFlux, Real.zero_rpow ha.ne', mul_zero, zero_mul]

/-- The endpoint extension of the flux is continuous. -/
theorem continuousAt_laplaceFlux_zero (a b z : ℝ) (ha : 0 < a) :
    ContinuousAt (laplaceFlux a b z) 0 := by
  apply ContinuousAt.mul
  · exact ((continuous_const.mul continuous_id).neg.rexp.continuousAt).mul
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le))
  · exact (continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl (by norm_num))

/-- The flux vanishes at infinity by exponential domination of its polynomial bound. -/
theorem tendsto_laplaceFlux_atTop (a b z : ℝ) (hz : 0 < z) :
    Tendsto (laplaceFlux a b z) atTop (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
  have hlimit : Tendsto
      (fun t : ℝ => 2 ^ n *
        (t ^ a * Real.exp (-z * t) + t ^ (a + (n : ℝ)) * Real.exp (-z * t)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a z hz).add
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a + n) z hz)).const_mul
          ((2 : ℝ) ^ n)
  apply squeeze_zero' _ _ hlimit
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    exact (mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _))
      (Real.rpow_pos_of_pos (add_pos zero_lt_one ht) _)).le
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have h := mul_le_mul_of_nonneg_left
      (one_add_rpow_le_polynomial (b - a) n hn.le t ht.le)
      (mul_pos (Real.exp_pos (-(z * t))) (Real.rpow_pos_of_pos ht a)).le
    rw [Real.rpow_add ht a (n : ℝ), Real.rpow_natCast]
    simp only [laplaceFlux, neg_mul] at h ⊢
    exact h.trans_eq (by ring)

/-- Exact flux derivative expressed by the first three integral moments. -/
theorem hasDerivAt_laplaceFlux (a b z t : ℝ) (ht : 0 < t) :
    HasDerivAt (laplaceFlux a b z)
      (a * laplaceKernelReal a b z t +
        (b - z) * laplaceKernelReal (a + 1) (b + 1) z t -
        z * laplaceKernelReal (a + 2) (b + 2) z t) t := by
  have ht1 : 0 < 1 + t := add_pos zero_lt_one ht
  have he := (((hasDerivAt_id t).const_mul z).neg.exp.mul
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne') :
      HasDerivAt (fun u : ℝ => u ^ a) (a * t ^ (a - 1)) t)).mul
    (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const (p := b - a) (Or.inl ht1.ne'))
  have heq : a * laplaceKernelReal a b z t +
      (b - z) * laplaceKernelReal (a + 1) (b + 1) z t -
      z * laplaceKernelReal (a + 2) (b + 2) z t =
      (Real.exp (-(z * t)) * -(z * 1) * t ^ a +
        Real.exp (-(z * t)) * (a * t ^ (a - 1))) * (1 + t) ^ (b - a) +
      Real.exp (-(z * t)) * t ^ a * ((0 + 1) *
        ((b - a) * (1 + t) ^ (b - a - 1))) := by
    have hpa : t ^ a = t ^ (a - 1) * t := by
      rw [← Real.rpow_add_one ht.ne']
      congr 1
      ring
    have hpb : (1 + t) ^ (b - a) = (1 + t) ^ (b - a - 1) * (1 + t) := by
      rw [← Real.rpow_add_one ht1.ne']
      congr 1
      ring
    simp only [laplaceKernelReal]
    rw [show a + 1 - 1 = (a - 1) + 1 by ring,
      show a + 2 - 1 = (a - 1) + 1 + 1 by ring,
      show b + 1 - (a + 1) - 1 = b - a - 1 by ring,
      show b + 2 - (a + 2) - 1 = b - a - 1 by ring,
      Real.rpow_add_one ht.ne', Real.rpow_add_one ht.ne',
      Real.rpow_add_one ht.ne']
    simp only [hpa, hpb]
    ring
  rw [heq]
  convert he using 1
  · rfl
  · dsimp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
    ring

/-- The flux moment relation, with zero endpoint terms. -/
theorem laplaceIntegral_moment_relation (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    a * laplaceIntegral a b z + (b - z) * laplaceIntegral (a + 1) (b + 1) z -
      z * laplaceIntegral (a + 2) (b + 2) z = 0 := by
  have h0 := integrableOn_laplaceKernelReal a b z ha hz
  have h1 := integrableOn_laplaceKernelReal (a + 1) (b + 1) z
    (add_pos ha zero_lt_one) hz
  have h2 := integrableOn_laplaceKernelReal (a + 2) (b + 2) z
    (by linarith only [ha]) hz
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousAt_laplaceFlux_zero a b z ha).continuousWithinAt
    (fun t ht => hasDerivAt_laplaceFlux a b z t ht)
    (((h0.const_mul a).add (h1.const_mul (b - z))).sub (h2.const_mul z))
    (tendsto_laplaceFlux_atTop a b z hz)
  rw [laplaceFlux_zero a b z ha, sub_self] at hf
  have hsub := integral_sub ((h0.const_mul a).add (h1.const_mul (b - z)))
    (h2.const_mul z)
  have hadd := integral_add (h0.const_mul a) (h1.const_mul (b - z))
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul, integral_const_mul] at hf
  exact hf

/-- Second derivative of the unnormalized integral by two simultaneous shifts. -/
theorem deriv_deriv_laplaceIntegral (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    deriv (deriv (laplaceIntegral a b)) z = laplaceIntegral (a + 2) (b + 2) z := by
  have h := (hasDerivAt_laplaceIntegral (a + 1) (b + 1) z
    (add_pos ha zero_lt_one) hz).neg
  have heq : deriv (laplaceIntegral a b) =ᶠ[𝓝 z]
      fun w => -laplaceIntegral (a + 1) (b + 1) w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact deriv_laplaceIntegral a b w ha hw
  have hd := (h.congr_of_eventuallyEq heq).deriv
  simpa only [neg_neg, show a + 1 + 1 = a + 2 by ring,
    show b + 1 + 1 = b + 2 by ring] using hd

/-- Kummer's equation for the unnormalized positive integral. -/
theorem laplaceIntegral_ode (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    z * deriv (deriv (laplaceIntegral a b)) z +
      (b - z) * deriv (laplaceIntegral a b) z - a * laplaceIntegral a b z = 0 := by
  rw [deriv_deriv_laplaceIntegral a b z ha hz, deriv_laplaceIntegral a b z ha hz]
  have h := laplaceIntegral_moment_relation a b z ha hz
  linear_combination -h

/-- Second derivative of the normalized integral at a positive argument. -/
theorem deriv_deriv_UIr (a : Pos) (b z : ℝ) (hz : 0 < z) :
    deriv (deriv (UIr a b)) z =
      (Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 2) (b + 2) z := by
  have h := (hasDerivAt_laplaceIntegral (a.1 + 1) (b + 1) z
    (add_pos a.2 zero_lt_one) hz).const_mul (-(Real.Gamma a.1)⁻¹)
  have heq : deriv (UIr a b) =ᶠ[𝓝 z]
      fun w => -(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact (hasDerivAt_UIr a b w hw).deriv
  have hd := (h.congr_of_eventuallyEq heq).deriv
  simpa only [neg_mul_neg, show a.1 + 1 + 1 = a.1 + 2 by ring,
    show b + 1 + 1 = b + 2 by ring] using hd

/-- Kummer's equation for the positive integral definition. -/
theorem UIr_ode (a : Pos) (b z : ℝ) (hz : 0 < z) :
    z * deriv (deriv (UIr a b)) z + (b - z) * deriv (UIr a b) z - a.1 * UIr a b z = 0 := by
  rw [deriv_deriv_UIr a b z hz, (hasDerivAt_UIr a b z hz).deriv]
  change z * ((Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 2) (b + 2) z) +
    (b - z) * (-(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) -
    a.1 * ((Real.Gamma a.1)⁻¹ * laplaceIntegral a.1 b z) = 0
  have h := laplaceIntegral_moment_relation a.1 b z a.2 hz
  linear_combination -(Real.Gamma a.1)⁻¹ * h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
