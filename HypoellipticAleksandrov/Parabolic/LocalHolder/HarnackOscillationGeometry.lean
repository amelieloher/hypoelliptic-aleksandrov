module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

/-! # Euclidean geometry of the oscillation cylinders -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Unit points map into the physical backward cylinder of radius `r`. -/
theorem parabolicAffine_mapsTo_backward_ball {N : ℕ} (T : ℝ) (v : PDE.Vec N)
    {r : ℝ} (hr : 0 < r) :
    MapsTo (parabolicAffine (T - r ^ 2) v r)
      (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1)
      (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v r)) := by
  intro z hz
  change (T - r ^ 2 + r ^ 2 * z.1, v + r • z.2) ∈ _
  constructor
  · have hs := sq_pos_of_pos hr
    constructor <;> nlinarith only [hs, hz.1.1, hz.1.2]
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    rw [add_sub_cancel_left, PDE.vecEuclideanNorm_smul, abs_of_pos hr]
    have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).mp hz.2
    simp only [sub_zero] at hn
    nlinarith only [hr, hn]

/-- Inverse coordinates of a physical point recover the point exactly. -/
theorem parabolicAffine_inverse_apply {N : ℕ} (T : ℝ) (v : PDE.Vec N)
    {r : ℝ} (hr : 0 < r) (z : TimeVelocity N) :
    parabolicAffine (T - r ^ 2) v r
      ((z.1 - (T - r ^ 2)) / r ^ 2, r⁻¹ • (z.2 - v)) = z := by
  apply Prod.ext
  · change T - r ^ 2 + r ^ 2 * ((z.1 - (T - r ^ 2)) / r ^ 2) = z.1
    field_simp [hr.ne']
    ring
  · change v + r • (r⁻¹ • (z.2 - v)) = z.2
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

/-- The half-radius backward cylinder corresponds to the later Harnack slab. -/
theorem backward_half_ball_inverse_mem {N : ℕ} (T : ℝ) (v : PDE.Vec N)
    {r : ℝ} (hr : 0 < r) {z : TimeVelocity N}
    (hz : z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
      (PDE.euclideanBall v (r / 2))) :
    ((z.1 - (T - r ^ 2)) / r ^ 2, r⁻¹ • (z.2 - v)) ∈
      Ioo (3 / 4 : ℝ) 1 ×ˢ PDE.euclideanBall 0 (1 / 2 : ℝ) := by
  constructor
  · constructor
    · rw [lt_div_iff₀ (sq_pos_of_pos hr)]
      nlinarith only [hz.1.1]
    · rw [div_lt_iff₀ (sq_pos_of_pos hr)]
      linarith only [hz.1.2]
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
    rw [sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr)).mp hz.2
    calc r⁻¹ * PDE.vecEuclideanNorm (z.2 - v) < r⁻¹ * (r / 2) :=
        mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)
      _ = 1 / 2 := by field_simp

end HypoellipticAleksandrov.Parabolic.LocalHolder
