module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometry

/-! # The literal parabolic distance and two-point cylinder geometry -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open KineticAleksandrov.LocalA

/-- The literal parabolic distance is nonnegative. -/
theorem parabolicDistance_nonneg {N : ℕ} (z z' : TimeVelocity N) :
    0 ≤ parabolicDistance z z' :=
  add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (PDE.vecEuclideanNorm_nonneg _)

/-- The time difference is bounded by the square of the parabolic distance. -/
theorem abs_time_sub_le_parabolicDistance_sq {N : ℕ} (z z' : TimeVelocity N) :
    |z.1 - z'.1| ≤ parabolicDistance z z' ^ 2 := by
  have hnorm := PDE.vecEuclideanNorm_nonneg (z.2 - z'.2)
  have hs := Real.sqrt_nonneg |z.1 - z'.1|
  have he := Real.sq_sqrt (abs_nonneg (z.1 - z'.1))
  unfold parabolicDistance
  rw [← Real.sqrt_eq_rpow]
  nlinarith only [hnorm, hs, he]

/-- The velocity difference is bounded by the parabolic distance. -/
theorem velocity_sub_le_parabolicDistance {N : ℕ} (z z' : TimeVelocity N) :
    PDE.vecEuclideanNorm (z.2 - z'.2) ≤ parabolicDistance z z' :=
  le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)

/-- Distinct points have strictly positive parabolic distance. -/
theorem parabolicDistance_pos {N : ℕ} {z z' : TimeVelocity N} (hne : z ≠ z') :
    0 < parabolicDistance z z' := by
  have hnon := parabolicDistance_nonneg z z'
  by_contra h
  have hz : parabolicDistance z z' = 0 := le_antisymm (not_lt.mp h) hnon
  have ht := abs_time_sub_le_parabolicDistance_sq z z'
  have hv := velocity_sub_le_parabolicDistance z z'
  rw [hz] at ht hv
  have ht0 : z.1 = z'.1 := sub_eq_zero.mp (abs_eq_zero.mp (by
    exact le_antisymm (by simpa only [show (0 : ℝ) ^ 2 = 0 by norm_num] using ht)
      (abs_nonneg _)))
  have hv0 : z.2 = z'.2 := sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp
    (le_antisymm hv (PDE.vecEuclideanNorm_nonneg _)))
  exact hne (Prod.ext ht0 hv0)

/-- A positive future margin can always be chosen below the fixed top time zero. -/
theorem exists_pair_top {N : ℕ} {z z' : TimeVelocity N}
    (hz : z.1 < 0) (hz' : z'.1 < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, max z.1 z'.1 < T ∧ T < 0 ∧ T - max z.1 z'.1 ≤ δ ^ 2 := by
  let t := max z.1 z'.1
  have ht : t < 0 := max_lt hz hz'
  let e := min (δ ^ 2) (-t) / 2
  have he : 0 < e := half_pos (lt_min (sq_pos_of_pos hδ) (neg_pos.mpr ht))
  have heδ : e ≤ δ ^ 2 :=
    (div_le_self (le_of_lt (lt_min (sq_pos_of_pos hδ) (neg_pos.mpr ht)))
      (by norm_num)).trans (min_le_left _ _)
  have het : e < -t := by
    have hmin := min_le_right (δ ^ 2) (-t)
    dsimp only [e]
    linarith only [hmin, ht]
  exact ⟨t + e, lt_add_of_pos_right t he, by linarith only [het],
    by simpa only [t, add_sub_cancel_left] using heδ⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
