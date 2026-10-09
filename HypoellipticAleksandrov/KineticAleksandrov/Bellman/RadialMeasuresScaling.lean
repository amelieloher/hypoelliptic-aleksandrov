module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasures
import Mathlib.Tactic

/-! # Exact transformation of weighted radial volume -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Inverse radius scaling gives the exact inverse homogeneous weight. -/
theorem bellmanRadiusWeight_inverse_scale (alpha r : ℝ) (hr : 0 < r)
    (s : BellmanPositiveTime) :
    bellmanRadiusWeight alpha ((bellmanRadialScale r hr).symm s) =
      ENNReal.ofReal (r ^ (alpha - 1)) * bellmanRadiusWeight alpha s := by
  change ENNReal.ofReal ((r⁻¹ * s.val) ^ (1 - alpha)) = _
  rw [Real.mul_rpow (inv_nonneg.mpr hr.le) s.property.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
  have he : (r⁻¹) ^ (1 - alpha) = r ^ (alpha - 1) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [he]
  rfl

/-- The radial pushforward factor is the degree-two-plus-alpha adjoint factor. -/
theorem map_bellmanRadiusMeasure_radialScale (alpha r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) (bellmanRadiusMeasure alpha) =
      ENNReal.ofReal (r ^ (alpha - 2)) • bellmanRadiusMeasure alpha := by
  unfold bellmanRadiusMeasure
  rw [bellman_map_withDensity _ _ _ (measurable_bellmanRadiusWeight alpha),
    map_bellmanPositiveTimeVolume_radialScale]
  have he : (fun s => bellmanRadiusWeight alpha ((bellmanRadialScale r hr).symm s)) =
      ENNReal.ofReal (r ^ (alpha - 1)) • bellmanRadiusWeight alpha :=
    funext (bellmanRadiusWeight_inverse_scale alpha r hr)
  rw [he, withDensity_smul_measure, withDensity_smul _
    (measurable_bellmanRadiusWeight alpha), smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  have hi : r⁻¹ = r ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
  rw [hi, ← Real.rpow_add hr]
  congr 2
  ring

end HypoellipticAleksandrov.KineticAleksandrov
