module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailMoments
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # Finite positive first moments forced by the angular integrated identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- A nonnegative angular solution of degree at least three has finite positive first moment. -/
theorem bellmanAngularFirstMoment_integrable (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hi : LocallyIntegrable f volume)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y) :
    IntegrableOn (fun z => z * f z) (Ioi 0) volume := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (3 * (h 0 + J 0)) 0
    (b := fun y : ℝ => y) (l := atTop)
  · intro y
    simpa only [pow_one] using (bellmanAngularMoment_intervalIntegrable hi 0 y 1).1
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hyp : 0 < y := by linarith
    have hb := bellmanAngularFirstMoment_bound β f h J hβ hi hf hh he hyp
    have hh0 := hh 0
    have hdiv : h 0 / y ≤ h 0 := by
      apply (div_le_iff₀ hyp).mpr
      nlinarith
    have hn : (∫ z in 0..y, ‖z * f z‖) = bellmanAngularFirstMoment f y := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hyp.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hf] with z hz hfz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz.1.le hfz)]
    rw [hn]
    linarith

/-- The first angular moment converges to the full positive first-moment integral. -/
theorem bellmanAngularFirstMoment_tendsto (f : ℝ → ℝ)
    (hi : IntegrableOn (fun z => z * f z) (Ioi 0) volume) :
    Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 (∫ z in Ioi 0, z * f z)) :=
  intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id

/-- The full positive first moment is nonnegative for a nonnegative density. -/
theorem bellmanAngularFirstMoment_total_nonneg (f : ℝ → ℝ)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) : 0 ≤ ∫ z in Ioi 0, z * f z := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hf] with z hz hfz
  exact mul_nonneg hz.le hfz

end HypoellipticAleksandrov.KineticAleksandrov
