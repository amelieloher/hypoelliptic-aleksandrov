module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesLog
import Mathlib.Tactic

/-! # Reweighting a homogeneous radial measure into a translation-invariant measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The exact weight which removes the radial density degree. -/
def bellmanRadialDegreeWeight (β : ℝ) (w : BellmanPositiveTime × ℝ) : ENNReal :=
  ENNReal.ofReal (w.1.val ^ (β - 4))

/-- The degree-removing radial weight is measurable. -/
theorem measurable_bellmanRadialDegreeWeight (β : ℝ) :
    Measurable (bellmanRadialDegreeWeight β) := by
  unfold bellmanRadialDegreeWeight
  fun_prop

/-- The exact degree weight at the inverse radial scaling. -/
theorem bellmanRadialDegreeWeight_inverse_scale (β r : ℝ) (hr : 0 < r)
    (w : BellmanPositiveTime × ℝ) :
    bellmanRadialDegreeWeight β
      (((bellmanRadialScale r hr).prodCongr (Homeomorph.refl ℝ)).symm w) =
      ENNReal.ofReal (r ^ (4 - β)) * bellmanRadialDegreeWeight β w := by
  change ENNReal.ofReal ((r⁻¹ * w.1.val) ^ (β - 4)) = _
  rw [Real.mul_rpow (inv_nonneg.mpr hr.le) w.1.property.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _),
    bellmanRadialDegreeWeight]
  have hp : (r⁻¹) ^ (β - 4) = r ^ (4 - β) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hp]

/-- The reciprocal degree factors multiply to one. -/
theorem bellmanRadial_degreeFactors_cancel (β r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (r ^ (β - 4)) * ENNReal.ofReal (r ^ (4 - β)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), ← Real.rpow_add hr]
  simp only [show β - 4 + (4 - β) = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]

/-- Reweighting the actual homogeneous coordinate measure makes radial scaling invariant. -/
theorem HasBellmanDensityDegree.map_reweighted_angularPullback {β : ℝ}
    {μ : Measure BellmanPuncturedPlane} (hμ : HasBellmanDensityDegree β μ)
    (r : ℝ) (hr : 0 < r) :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl ℝ))
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) =
      (bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β) := by
  rw [bellman_map_withDensity _ _ _ (measurable_bellmanRadialDegreeWeight β),
    hμ.map_angularPullback r hr, withDensity_smul_measure]
  have he : (fun w => bellmanRadialDegreeWeight β
      (((bellmanRadialScale r hr).prodCongr (Homeomorph.refl ℝ)).symm w)) =
      ENNReal.ofReal (r ^ (4 - β)) • bellmanRadialDegreeWeight β := by
    funext w
    exact bellmanRadialDegreeWeight_inverse_scale β r hr w
  rw [he, withDensity_smul _ (measurable_bellmanRadialDegreeWeight β), smul_smul,
    bellmanRadial_degreeFactors_cancel β r hr, one_smul]

/-- The literal reweighted homogeneous measure in log-radius/angular coordinates. -/
def bellmanLogAngularMeasure (β : ℝ) (μ : Measure BellmanPuncturedPlane) :
    Measure (ℝ × ℝ) :=
  Measure.map bellmanLogAngularHomeomorph
    ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β))

/-- Homogeneity gives first-coordinate translation invariance of the actual log-radius
measure. -/
theorem HasBellmanDensityDegree.logAngularMeasure_invariant {β : ℝ}
    {μ : Measure BellmanPuncturedPlane} (hμ : HasBellmanDensityDegree β μ) (a : ℝ) :
    Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2))
      (bellmanLogAngularMeasure β μ) = bellmanLogAngularMeasure β μ := by
  let S := (bellmanRadialScale (Real.exp a) (Real.exp_pos a)).prodCongr (Homeomorph.refl ℝ)
  rw [bellmanLogAngularMeasure,
    Measure.map_map (by fun_prop) bellmanLogAngularHomeomorph.measurable]
  have he : (fun q : ℝ × ℝ => (a + q.1, q.2)) ∘ bellmanLogAngularHomeomorph =
      bellmanLogAngularHomeomorph ∘ S := by
    funext w
    change (a + Real.log w.1.val, w.2) = (Real.log (Real.exp a * w.1.val), w.2)
    rw [Real.log_mul (Real.exp_ne_zero a) w.1.property.ne', Real.log_exp]
  rw [he, ← Measure.map_map bellmanLogAngularHomeomorph.measurable S.measurable,
    hμ.map_reweighted_angularPullback (Real.exp a) (Real.exp_pos a)]

end HypoellipticAleksandrov.KineticAleksandrov
