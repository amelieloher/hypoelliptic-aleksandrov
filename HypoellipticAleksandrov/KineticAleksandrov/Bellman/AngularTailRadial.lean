module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesRadial
import Mathlib.Tactic

/-! # Radial scaling used in the angular tail estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The degree-dependent radial measure transforms with exponent beta minus four. -/
theorem bellmanRadialWeight_map_scale (β r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) (bellmanRadialWeight β) =
      ENNReal.ofReal (r ^ (β - 4)) • bellmanRadialWeight β := by
  rw [bellmanRadialWeight, bellman_map_withDensity _ _ _ (by fun_prop),
    map_bellmanPositiveTimeVolume_radialScale, withDensity_smul_measure]
  have he : (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (((bellmanRadialScale r hr).symm s).val ^ (3 - β))) =
      ENNReal.ofReal (r ^ (β - 3)) •
        (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (3 - β))) := by
    funext s
    change ENNReal.ofReal ((r⁻¹ * s.val) ^ (3 - β)) = _
    rw [Real.mul_rpow (inv_nonneg.mpr hr.le) s.property.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)]
    have hp : (r⁻¹) ^ (3 - β) = r ^ (β - 3) := by
      rw [← Real.rpow_neg_eq_inv_rpow]
      congr 1
      ring
    rw [hp]
    rfl
  rw [he, withDensity_smul _ (by fun_prop), smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  have hp : r⁻¹ * r ^ (β - 3) = r ^ (β - 4) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  rw [hp]

/-- A radial strip at velocity y has exactly the source tail weight times a fixed positive
mass. -/
theorem bellmanRadialWeight_velocity_strip (β y : ℝ) (hy : 0 < y) :
    bellmanRadialWeight β {s | 1 ≤ y * s.val ∧ y * s.val ≤ 2} =
      ENNReal.ofReal (y ^ (β - 4)) *
        bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2} := by
  have hm : MeasurableSet {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} := by
    measurability
  have he := congrArg (fun μ : Measure BellmanPositiveTime =>
      μ {s | 1 ≤ s.val ∧ s.val ≤ 2}) (bellmanRadialWeight_map_scale β y hy)
  rw [Measure.map_apply (bellmanRadialScale y hy).measurable hm,
    Measure.smul_apply, smul_eq_mul] at he
  exact he

end HypoellipticAleksandrov.KineticAleksandrov
