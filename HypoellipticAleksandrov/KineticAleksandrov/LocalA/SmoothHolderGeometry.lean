module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullback
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometryCompact
import Mathlib.Tactic

/-! # Geometry and oscillation for smooth kinetic Hölder normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder

/-- A fixed-position outer parabolic slice is contained in the three-quarter cylinder. -/
theorem holder_slice_mem_inner {d : ℕ} (x : PDE.Vec d)
    (hx : x ∈ PDE.euclideanBall 0 (1 / 8 : ℝ)) (z : TimeVelocity d)
    (hz : z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
      (PDE.euclideanBall 0 (3 / 4 : ℝ))) :
    (⟨z.1, x, z.2⟩ : KineticPoint d) ∈
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (3 / 4) := by
  change (0 : ℝ) - (3 / 4) ^ 2 < z.1 ∧ z.1 < 0 ∧
    z.2 ∈ PDE.euclideanBall 0 (3 / 4) ∧
    relativePosition (⟨0, 0, 0⟩ : KineticPoint d) ⟨z.1, x, z.2⟩ ∈
      PDE.euclideanBall 0 ((3 / 4) ^ 3)
  refine ⟨by linarith only [hz.1.1], hz.1.2, hz.2, ?_⟩
  simpa only [relativePosition, sub_zero, smul_zero] using
    PDE.euclideanBall_mono (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ (3 / 4) ^ 3) hx

/-- A point in the half kinetic cylinder supplies precisely the inner slice coordinates. -/
theorem holder_half_coordinates {d : ℕ} {P : KineticPoint d}
    (hP : P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (1 / 2)) :
    (P.time, P.velocity) ∈ scalarParabolicOpenCylinder (-1 / 4) 0
      (PDE.euclideanBall 0 (1 / 2 : ℝ)) ∧
    P.position ∈ PDE.euclideanBall 0 (1 / 8 : ℝ) := by
  rcases hP with ⟨ht, ht', hv, hx⟩
  refine ⟨⟨⟨by linarith only [ht], ht'⟩, hv⟩, ?_⟩
  simpa only [relativePosition, sub_zero, smul_zero,
    show (1 / 2 : ℝ) ^ 3 = 1 / 8 by norm_num] using hx

/-- Kinetic affine normalization transports every positive subradius exactly. -/
theorem kineticAffine_mem_radius {d : ℕ} (P₀ P : KineticPoint d)
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    kineticAffine P₀ R P ∈ backwardCylinder P₀ (R * r) ↔
      P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) r := by
  rw [mem_backwardCylinder_iff, mem_backwardCylinder_iff]
  rw [relativePosition_kineticAffine]
  simp only [kineticAffine_time, kineticAffine_velocity,
    relativePosition, sub_zero, smul_zero]
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (mul_pos hR hr),
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos (mul_pos hR hr) 3),
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)]
  simp only [add_sub_cancel_left, sub_zero, PDE.vecEuclideanNorm_smul,
    abs_of_pos hR, abs_of_pos (pow_pos hR 3), mul_pow]
  have hR2 := pow_pos hR 2
  have hR3 := pow_pos hR 3
  constructor
  · rintro ⟨ha, hb, hv, hx⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [ha, hb, hv, hx, hR, hR2, hR3]
  · rintro ⟨ha, hb, hv, hx⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith only [ha, hb, hv, hx, hR, hR2, hR3]

/-- Pullback leaves the oscillation unchanged on corresponding full cylinders. -/
theorem oscillationOn_kineticPullback {d : ℕ} (u : KineticPoint d → ℝ)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) :
    oscillationOn (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) =
      oscillationOn u (backwardCylinder P₀ R) := by
  have he : kineticPullback u P₀ R ''
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 =
      u '' backwardCylinder P₀ R := by
    simp only [kineticPullback, Function.comp_def]
    rw [← image_image u (kineticAffine P₀ R),
      kineticAffine_image_unitCylinder P₀ hR]
  simp only [oscillationOn, he]

/-- Continuity on the closed outer cylinder is preserved under normalization. -/
theorem continuousOn_kineticPullback_closure {d : ℕ} {u : KineticPoint d → ℝ}
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closure (backwardCylinder P₀ R))) :
    ContinuousOn (kineticPullback u P₀ R)
      (closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) := by
  apply hu.comp (continuous_kineticAffine P₀ R).continuousOn
  intro P hP
  rw [← kineticAffine_image_closedUnitCylinder P₀ hR]
  exact mem_image_of_mem _ hP

/-- Kinetic increments scale by one power of the physical radius. -/
theorem kineticIncrement_kineticAffine {d : ℕ} (P₀ P Q : KineticPoint d)
    {R : ℝ} (hR : 0 < R) :
    kineticIncrement P₀ (kineticAffine P₀ R P) (kineticAffine P₀ R Q) / R =
      kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q := by
  have ht : (kineticAffine P₀ R P).time - (kineticAffine P₀ R Q).time =
      R ^ 2 * (P.time - Q.time) := by simp only [kineticAffine_time]; ring
  have hv : (kineticAffine P₀ R P).velocity - (kineticAffine P₀ R Q).velocity =
      R • (P.velocity - Q.velocity) := by simp only [kineticAffine_velocity]; module
  have hx : (kineticAffine P₀ R P).position - (kineticAffine P₀ R Q).position -
      ((kineticAffine P₀ R P).time - (kineticAffine P₀ R Q).time) • P₀.velocity =
      R ^ 3 • (P.position - Q.position) := by
    simp only [kineticAffine_position, ht]
    module
  have hp2 : (R ^ 2) ^ (1 / 2 : ℝ) = R := by
    rw [← Real.rpow_natCast_mul hR.le]
    norm_num
  have hp3 : (R ^ 3) ^ (1 / 3 : ℝ) = R := by
    rw [← Real.rpow_natCast_mul hR.le]
    norm_num
  simp only [kineticIncrement]
  rw [hx, ht, hv]
  simp only [abs_mul, abs_of_pos (pow_pos hR 2),
    PDE.vecEuclideanNorm_smul, abs_of_pos hR, abs_of_pos (pow_pos hR 3),
    Real.mul_rpow (pow_nonneg hR.le 2) (abs_nonneg (P.time - Q.time)),
    Real.mul_rpow (pow_nonneg hR.le 3) (PDE.vecEuclideanNorm_nonneg _),
    hp2, hp3, smul_zero, sub_zero]
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
