module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.Tactic

/-! # Density-degree two for the actual fundamental measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Positive kinetic dilation is a homeomorphism of the actual punctured plane. -/
def bellmanDilationHomeomorph (r : ℝ) (hr : 0 < r) :
    BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane where
  toFun := bellmanDilation r hr
  invFun := bellmanDilation r⁻¹ (inv_pos.mpr hr)
  left_inv q := by
    apply Subtype.ext
    change bellmanPlaneDilation r⁻¹ (bellmanPlaneDilation r q.val) = q.val
    rw [bellmanPlaneDilation_comp, inv_mul_cancel₀ hr.ne']
    simp only [bellmanPlaneDilation, one_pow, one_mul, Prod.eta]
  right_inv q := by
    apply Subtype.ext
    change bellmanPlaneDilation r (bellmanPlaneDilation r⁻¹ q.val) = q.val
    rw [bellmanPlaneDilation_comp, mul_inv_cancel₀ hr.ne']
    simp only [bellmanPlaneDilation, one_pow, one_mul, Prod.eta]
  continuous_toFun := by unfold bellmanDilation; fun_prop
  continuous_invFun := by unfold bellmanDilation; fun_prop

/-- The degree-two mass scaling is proved for all measurable punctured-plane sets. -/
theorem bellmanFundamentalMeasure_densityDegree :
    HasBellmanDensityDegree 2 bellmanFundamentalMeasure := by
  intro r hr E hE
  let D := bellmanDilationHomeomorph r hr
  have hm : MeasurableSet (D '' E) := D.measurableEmbedding.measurableSet_image.mpr hE
  have hi : D ⁻¹' (D '' E) = E := D.injective.preimage_image E
  have hscale : ENNReal.ofReal (r⁻¹ ^ 4) * bellmanFundamentalMeasure (D '' E) =
      ENNReal.ofReal (r⁻¹ ^ 2) * bellmanFundamentalMeasure E := by
    calc
      _ = ∫⁻ q in D '' E, bellmanFundamentalDensity q
          ∂(Measure.map D bellmanPuncturedVolume) := by
        rw [show Measure.map D bellmanPuncturedVolume =
          ENNReal.ofReal (r⁻¹ ^ 4) • bellmanPuncturedVolume from
            map_bellmanPuncturedVolume_dilation r hr, setLIntegral_smul_measure,
          bellmanFundamentalMeasure, withDensity_apply _ hm]
        rfl
      _ = ∫⁻ q in E, bellmanFundamentalDensity (D q) ∂bellmanPuncturedVolume := by
        rw [setLIntegral_map hm measurable_bellmanFundamentalDensity D.measurable, hi]
      _ = _ := by
        change (∫⁻ q in E, bellmanFundamentalDensity (bellmanDilation r hr q)
          ∂bellmanPuncturedVolume) = _
        simp only [bellmanFundamentalDensity_dilation]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          bellmanFundamentalMeasure, withDensity_apply _ hE]
  have hc : ENNReal.ofReal (r ^ 4) * ENNReal.ofReal (r⁻¹ ^ 4) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 4)]
    simp only [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one]
  have hp : ENNReal.ofReal (r ^ 4) * ENNReal.ofReal (r⁻¹ ^ 2) =
      ENNReal.ofReal (r ^ (4 - (2 : ℝ))) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 4)]
    norm_num only [show (4 : ℝ) - 2 = 2 from by norm_num, Real.rpow_two]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal (r ^ 4) * ENNReal.ofReal (r⁻¹ ^ 4)) *
        bellmanFundamentalMeasure (D '' E) := by rw [hc, one_mul]; rfl
    _ = ENNReal.ofReal (r ^ 4) *
        (ENNReal.ofReal (r⁻¹ ^ 2) * bellmanFundamentalMeasure E) := by
      rw [mul_assoc, hscale]
    _ = _ := by rw [← mul_assoc, hp]

end HypoellipticAleksandrov.KineticAleksandrov
