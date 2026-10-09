module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.EulerIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
# Beta evaluation on the positive half-line

The fractional linear substitution carries the positive half-line onto the unit interval.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set MeasureTheory

/-- Fractional linear coordinate on the positive half-line. -/
def betaCoordinate (t : ℝ) : ℝ := t / (1 + t)

/-- Derivative of the fractional linear coordinate. -/
theorem hasDerivAt_betaCoordinate (t : ℝ) (ht : 0 < t) :
    HasDerivAt betaCoordinate ((1 + t) ^ (-2 : ℝ)) t := by
  have h := (hasDerivAt_id t).div ((hasDerivAt_const t 1).add (hasDerivAt_id t))
    (ne_of_gt (by linarith : 0 < 1 + t))
  convert h using 1
  · rfl
  · change (1 + t) ^ (-2 : ℝ) = (1 * (1 + t) - t * (0 + 1)) / (1 + t) ^ 2
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by linarith : 0 ≤ 1 + t), Real.rpow_two]
    field_simp
    ring

/-- The coordinate is injective on the positive half-line. -/
theorem betaCoordinate_injOn : InjOn betaCoordinate (Ioi 0) := by
  intro x hx y hy h
  change 0 < x at hx
  change 0 < y at hy
  dsimp [betaCoordinate] at h
  have h' := (div_eq_div_iff (by linarith : 1 + x ≠ 0)
    (by linarith : 1 + y ≠ 0)).mp h
  nlinarith

/-- The image of the positive half-line is the open unit interval. -/
theorem betaCoordinate_image : betaCoordinate '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < t at ht
    dsimp [betaCoordinate]
    constructor
    · exact div_pos ht (by linarith)
    · exact (div_lt_one (by linarith : 0 < 1 + t)).mpr (by linarith)
  · intro hu
    refine ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2), ?_⟩
    dsimp [betaCoordinate]
    have hn : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu.2)
    have hd : 1 + u / (1 - u) ≠ 0 := ne_of_gt
      (add_pos zero_lt_one (div_pos hu.1 (sub_pos.mpr hu.2)))
    field_simp [hn, hd]
    ring

/-- Pullback of the Beta weight including the Jacobian. -/
theorem betaCoordinate_weight (a c t : ℝ) (ht : 0 < t) :
    |(1 + t) ^ (-2 : ℝ)| • betaWeight a c (betaCoordinate t) =
      t ^ (a - 1) * (1 + t) ^ (-a - c) := by
  have hp : 0 < 1 + t := by linarith
  have he : 1 - betaCoordinate t = (1 + t)⁻¹ := by
    dsimp [betaCoordinate]
    field_simp
    ring
  rw [smul_eq_mul, abs_of_pos (Real.rpow_pos_of_pos hp _), betaWeight, he,
    betaCoordinate, Real.div_rpow ht.le hp.le, Real.inv_rpow hp.le,
    div_eq_mul_inv, ← Real.rpow_neg hp.le]
  rw [← Real.rpow_neg hp.le]
  rw [mul_left_comm, mul_assoc, ← Real.rpow_add hp, ← Real.rpow_add hp]
  congr 2
  ring

/-- Integrability of the half-line Beta weight. -/
theorem integrableOn_betaHalf (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-a - c)) (Ioi 0) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (hasDerivAt_betaCoordinate t ht).hasDerivWithinAt)
    betaCoordinate_injOn (betaWeight a c)).mp
    (by rw [betaCoordinate_image]; exact
      (intervalIntegrable_betaWeight a c ha hc).1.mono_set Ioo_subset_Ioc_self)
  exact h.congr_fun (fun t ht => betaCoordinate_weight a c t ht) measurableSet_Ioi

/-- Evaluation of the half-line Beta integral. -/
theorem integral_betaHalf (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * (1 + t) ^ (-a - c)) =
      Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (hasDerivAt_betaCoordinate t ht).hasDerivWithinAt)
    betaCoordinate_injOn (betaWeight a c)
  rw [betaCoordinate_image] at h
  have he := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (fun t ht => betaCoordinate_weight a c t ht)
  rw [he] at h
  rw [← h, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1), integral_betaWeight a c ha hc]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
