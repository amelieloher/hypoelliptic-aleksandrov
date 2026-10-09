module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeScaling
import Mathlib.Tactic

/-! # Degree-two scaling of the time-integrated Gaussian density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Time change of variables combines degree four of the kernel with degree two of time. -/
theorem bellmanFundamentalDensity_scaled_identity (r : ℝ) (hr : 0 < r)
    (q : BellmanPuncturedPlane) :
    ENNReal.ofReal ((r ^ 2)⁻¹) * bellmanFundamentalDensity (bellmanDilation r hr q) =
      ENNReal.ofReal (r⁻¹ ^ 4) * bellmanFundamentalDensity q := by
  have hf : Measurable (fun t : BellmanPositiveTime => ENNReal.ofReal
      (bellmanGaussianKernel t (bellmanDilation r hr q).val)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_bellmanGaussianKernel.comp
        (continuous_id.prodMk continuous_const)).measurable
  calc
    _ = ∫⁻ t, ENNReal.ofReal (bellmanGaussianKernel t (bellmanDilation r hr q).val)
        ∂(Measure.map (bellmanScaledTime r hr) bellmanPositiveTimeVolume) := by
      rw [map_bellmanPositiveTimeVolume_scaled, lintegral_smul_measure]
      rfl
    _ = ∫⁻ t, ENNReal.ofReal (bellmanGaussianKernel (bellmanScaledTime r hr t)
        (bellmanDilation r hr q).val) ∂bellmanPositiveTimeVolume :=
      lintegral_map hf (measurable_bellmanScaledTime r hr)
    _ = _ := by
      simp only [bellmanDilation_val, bellmanGaussianKernel_scaling,
        ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr.le) 4)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The actual fundamental density has degree two under positive kinetic dilation. -/
theorem bellmanFundamentalDensity_dilation (r : ℝ) (hr : 0 < r)
    (q : BellmanPuncturedPlane) :
    bellmanFundamentalDensity (bellmanDilation r hr q) =
      ENNReal.ofReal (r⁻¹ ^ 2) * bellmanFundamentalDensity q := by
  have hc : ENNReal.ofReal (r ^ 2) * ENNReal.ofReal ((r ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 2),
      mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), ENNReal.ofReal_one]
  have hp : ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (r⁻¹ ^ 4) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 2)]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal (r ^ 2) * ENNReal.ofReal ((r ^ 2)⁻¹)) *
        bellmanFundamentalDensity (bellmanDilation r hr q) := by rw [hc, one_mul]
    _ = ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal (r⁻¹ ^ 4) * bellmanFundamentalDensity q) := by
      rw [mul_assoc, bellmanFundamentalDensity_scaled_identity r hr q]
    _ = _ := by rw [← mul_assoc, hp]

end HypoellipticAleksandrov.KineticAleksandrov
