module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.LogIntegration
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Integrating killed slab bounds over all positive times -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal

/-- The killed power moment is finite whenever its exponent at zero is integrable. -/
theorem killed_power_moment_finite {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T))) < ⊤ := by
  have hi : IntegrableOn (fun T : ℝ => T ^ (δ - 1) * Real.exp (-k * T)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := δ - 1) (by linarith) (by norm_num) hk
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
    exact mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_pos _).le

/-- The inverse-time weight combines with the killed slab power exactly. -/
theorem lintegral_inv_killed_power (δ k : ℝ) (A : ℝ≥0∞) :
    (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal T⁻¹ *
      (A * ENNReal.ofReal (T ^ δ * Real.exp (-k * T)))) =
    A * ∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T)) := by
  have hm : Measurable (fun T : ℝ => ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_id.pow_const _).mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_id)))
  rw [← lintegral_const_mul A hm]
  refine setLIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
  have ht : T ^ (δ - 1) = T⁻¹ * T ^ δ := by
    rw [Real.rpow_sub hT, Real.rpow_one]
    field_simp
  rw [ht, ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hT.le)
    (Real.rpow_nonneg hT.le _)), ENNReal.ofReal_mul (inv_nonneg.mpr hT.le),
    ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
  ring

/-- Logarithmic averaging over all positive times, obtained by increasing finite horizons. -/
theorem log_mul_measure_univ_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {h : X → ℝ} (hh : Measurable h)
    (hpos : ∀ x, 0 < h x) :
    ENNReal.ofReal (Real.log 2) * ν univ ≤
      ∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal T⁻¹ * ν {x | T < h x ∧ h x < 2 * T} := by
  have hm : Monotone (fun S : ℝ => {x | h x < S}) := by
    intro S R hSR x hx
    exact hx.trans_le hSR
  have hu : (⋃ S : ℝ, {x | h x < S}) = univ := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨h x + 1, by linarith⟩
  rw [← hu, hm.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun S => (log_mul_measure_le ν hh hpos S).trans ?_
  exact lintegral_mono_set (fun T hT => hT.1)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
