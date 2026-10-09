module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Parabolic.Jacobian
public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# One-sided area formula for the parabolic normal map

This module records the exact product-volume normalization of the
slope--intercept wedge and specializes the one-sided area formula to the
parabolic normal map.  The `TimeVelocity` volume is the product
Lebesgue measure; no competing Haar instance is introduced.  The area bound
does not assume injectivity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

/-- The slope--intercept wedge is measurable. -/
theorem measurableSet_slopeInterceptWedge (d : ℕ) (M : ℝ) :
    MeasurableSet (slopeInterceptWedge d M) :=
  measurableSet_Ioo.prod
    (PDE.measurableSet_euclideanBall (0 : PDE.Vec d) (M / 4))

/-- The exact product-volume normalization of the slope--intercept wedge. -/
theorem volume_slopeInterceptWedge {d : ℕ} {M : ℝ} (hM : 0 < M) :
    volume (slopeInterceptWedge d M) =
      ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / 4) ^ d) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1)) := by
  unfold slopeInterceptWedge
  have hM4 : 0 < M / 4 := div_pos hM (by norm_num)
  have hinterval : 3 * M / 4 - M / 2 = M / 4 := by ring
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, hinterval,
    PDE.volume_euclideanBall_eq_unit_mul_of_pos (0 : PDE.Vec d) hM4]

/-- The wedge volume with its time and velocity scaling combined into one power. -/
theorem volume_slopeInterceptWedge_eq {d : ℕ} {M : ℝ} (hM : 0 < M) :
    volume (slopeInterceptWedge d M) =
      ENNReal.ofReal ((M / 4) ^ (d + 1)) *
        volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
  rw [volume_slopeInterceptWedge hM]
  have hM4 : 0 ≤ M / 4 := (div_pos hM (by norm_num)).le
  calc
    ENNReal.ofReal (M / 4) *
        (ENNReal.ofReal ((M / 4) ^ d) * volume (PDE.euclideanBall (0 : PDE.Vec d) 1)) =
        (ENNReal.ofReal (M / 4) * ENNReal.ofReal ((M / 4) ^ d)) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      rw [mul_assoc]
    _ = ENNReal.ofReal ((M / 4) * (M / 4) ^ d) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      rw [← ENNReal.ofReal_mul hM4]
    _ = ENNReal.ofReal ((M / 4) ^ (d + 1)) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
      congr 2
      rw [pow_succ]
      ring

/-- The one-sided area formula for the actual parabolic normal map on its sign set.

No injectivity or finiteness hypothesis is required. -/
theorem volume_parabolicNormalMap_image_le_lintegral_abs_det_fderiv
    {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
    (T : ℝ) (y₀ : PDE.Vec d) :
    volume (parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u) ≤
      ∫⁻ z in parabolicSignSet T y₀ u,
        ENNReal.ofReal |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ∂volume := by
  apply MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv volume
  · exact measurableSet_parabolicSignSet hu T y₀
  · intro z _hz
    simpa only [parabolicNormalMap_fderiv hu y₀ z] using
      (parabolicNormalMap_hasFDerivAt hu y₀ z).hasFDerivWithinAt

end HypoellipticAleksandrov.Parabolic
