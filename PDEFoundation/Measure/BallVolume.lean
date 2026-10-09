module

public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Volume of explicit round balls

Positivity, finiteness, and exact affine scaling for the native round-ball
geometry.
-/

@[expose] public section

namespace PDE

open MeasureTheory

theorem volume_euclideanBall_ne_top {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume (euclideanBall x R) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    ((isCompact_euclideanClosedBall x hR).measure_ne_top
      (μ := volume)) ?_
  exact measure_mono
    (euclideanBall_subset_euclideanClosedBall x R)

theorem volume_euclideanBall_pos {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < volume (euclideanBall x R) :=
  (isOpen_euclideanBall x R).measure_pos volume
    (euclideanBall_nonempty x hR)

theorem volume_euclideanBall_toReal_pos {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < (volume (euclideanBall x R)).toReal := by
  exact ENNReal.toReal_pos
    (volume_euclideanBall_pos x hR).ne'
    (volume_euclideanBall_ne_top x hR.le)

theorem isFiniteMeasure_volumeOn_euclideanBall {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (volumeOn (euclideanBall x R)) := by
  simpa [volumeOn] using
    (isFiniteMeasure_restrict.mpr
      (volume_euclideanBall_ne_top x hR))

theorem volume_euclideanBall_eq_unit_mul_of_pos {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    volume (euclideanBall x R) =
      ENNReal.ofReal (R ^ d) *
        volume (euclideanBall (0 : Vec d) 1) := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos x hR,
    volume_translateSet_eq,
    volume_smul_set_of_nonneg hR.le]

theorem volume_euclideanBall_toReal_eq_unit_mul_of_pos {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    (volume (euclideanBall x R)).toReal =
      R ^ d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal := by
  rw [volume_euclideanBall_eq_unit_mul_of_pos x hR,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hR.le d)]

/-- The ratio of the volumes of two positive-radius round balls is the
corresponding radius ratio to the dimension, independently of their centers. -/
theorem volume_euclideanBall_toReal_div_eq_div_pow {d : ℕ}
    (x y : Vec d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (volume (euclideanBall x R)).toReal /
        (volume (euclideanBall y r)).toReal =
      (R / r) ^ d := by
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos x hR,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos y hr,
    div_pow]
  have hunit :
      (volume (euclideanBall (0 : Vec d) 1)).toReal ≠ 0 :=
    (volume_euclideanBall_toReal_pos
      (0 : Vec d) (by norm_num)).ne'
  field_simp [hunit, hr.ne']

end PDE
