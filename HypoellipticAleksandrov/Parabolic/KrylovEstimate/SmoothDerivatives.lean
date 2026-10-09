module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

/-! # Selected scalar and joint derivatives agree on smooth functions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Filter
open scoped Topology

private theorem coordinate_single_smooth {N : ℕ} (w : TimeVelocity N → ℝ)
    (hw : ContDiff ℝ 2 w) (c : TimeVelocityCoord N) (z : TimeVelocity N) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv (Pi.single c 1) w z =
      fderiv ℝ w z (timeVelocityBasis c) := by
  have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex N) c w z (by
      simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, zero_add] using
        (hw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt)
  have hzero : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex N) w = w := by
    funext y
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero w y
  simpa only [zero_add, hzero] using hs

/-- The scalar time derivative equals the joint directional derivative. -/
theorem scalarTimeDerivative_eq_timeDerivative
    {N : ℕ} (w : TimeVelocity N → ℝ) (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarTimeDerivative w z = timeDerivative w z := by
  rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hw z,
    coordinate_single_smooth w hw]
  rfl
/-- The scalar gradient equals the joint velocity gradient. -/
theorem scalarSpatialGradient_eq_velocityGradient
    {N : ℕ} (w : TimeVelocity N → ℝ) (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarSpatialGradient w z = velocityGradient w z := by
  ext i
  rw [scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw z i,
    coordinate_single_smooth w hw]
  rfl

/-- The scalar Hessian equals the joint velocity Hessian. -/
theorem scalarSpatialHessian_eq_velocityHessian
    {N : ℕ} (w : TimeVelocity N → ℝ) (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    scalarSpatialHessian w z = velocityHessian w z := by
  ext i j
  rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw z i j]
  have ho : TimeVelocityMultiIndex.order
      (Pi.single (velocityCoord j) 1 : TimeVelocityMultiIndex N) + 1 = 2 := by
    simp only [TimeVelocityMultiIndex.order_single]
  have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) w z (by
      simpa only [TimeVelocityMultiIndex.order_single, Nat.cast_one,
        show (1 : WithTop ℕ∞) + 1 = 2 from rfl] using! hw.contDiffAt)
  have hf : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (Pi.single (velocityCoord j) 1) w =
      (fun y => fderiv ℝ w y (timeVelocityBasis (velocityCoord j))) := by
    funext y
    exact coordinate_single_smooth w hw _ y
  rw [hs, hf]
  have hd := ((hw.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) z
  rw [fderiv_clm_apply hd (differentiableAt_const (c :=
    timeVelocityBasis (velocityCoord j)))]
  simp [timeVelocityBasis_velocity, velocityHessian, PDE.basisVec]

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
