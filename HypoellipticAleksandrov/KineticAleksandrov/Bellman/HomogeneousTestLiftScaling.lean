module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLift
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
import Mathlib.Tactic

/-! # Exact homogeneity of the literal radial test integral -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Radial substitution gives the required function degree of the actual test integral. -/
theorem bellman_lift_scaling (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ) :
    lift alpha zeta (bellmanPlaneDilation s q) = s ^ alpha * lift alpha zeta q := by
  let F : BellmanPositiveTime → ℝ := fun r =>
    r.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val q)
  have he (r : BellmanPositiveTime) :
      F (bellmanRadialScale s hs r) = s ^ (-1 - alpha) *
        (r.val ^ (-1 - alpha) *
          zeta (bellmanPlaneDilation r.val (bellmanPlaneDilation s q))) := by
    dsimp [F, bellmanRadialScale]
    rw [Real.mul_rpow hs.le r.property.le, bellmanPlaneDilation_comp]
    rw [mul_comm r.val s]
    ring
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hs (-1 - alpha)).ne'
  calc
    s ^ (-1 - alpha) * lift alpha zeta (bellmanPlaneDilation s q) =
        ∫ r, F (bellmanRadialScale s hs r) ∂bellmanPositiveTimeVolume := by
      simp_rw [he]
      rw [integral_const_mul]
      rfl
    _ = s⁻¹ * lift alpha zeta q := by
      rw [← (bellmanRadialScale s hs).measurableEmbedding.integral_map,
        map_bellmanPositiveTimeVolume_radialScale, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le)]
      rfl
    _ = s ^ (-1 - alpha) * (s ^ alpha * lift alpha zeta q) := by
      rw [← mul_assoc, ← Real.rpow_add hs]
      have ha : -1 - alpha + alpha = (-1 : ℝ) := by ring
      rw [ha, Real.rpow_neg_one]

end HypoellipticAleksandrov.KineticAleksandrov
