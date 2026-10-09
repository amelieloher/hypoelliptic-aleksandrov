module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBounds
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Dimensionless scalar covariance estimates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

/-- The upper covariance bound for unit ellipticity, in Loewner order. -/
theorem ghat_unit_upper {theta : ℝ} (ht : |theta| ≤ 1) :
    ghat 1 theta ≤ (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have ht0 := (abs_le.mp ht).1
  have ht1 := (abs_le.mp ht).2
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  have hcube : theta ^ 3 ≤ 1 := by
    by_cases h0 : 0 ≤ theta
    · simpa using pow_le_pow_left₀ h0 ht1 3
    · have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg theta) (not_le.mp h0).le
      nlinarith
  have hc : |theta / 64 + theta ^ 2 / 2| ≤ 33 / 64 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg theta]
  have ha : |-(theta / 64 + theta ^ 2 / 2)| ≤
      2 - ((1 + theta ^ 2) / 64 + theta ^ 3 / 3) := by
    rw [abs_neg]
    linarith
  have hb : |-(theta / 64 + theta ^ 2 / 2)| ≤ 2 - (1 / 64 + theta) := by
    rw [abs_neg]
    linarith
  apply Matrix.le_iff.mpr
  convert posSemidef_two_of_diagonal ha hb using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

/-- Upper covariance bound on the short negative cutoff strip. -/
theorem ghat_unit_cutoff_upper {theta : ℝ}
    (ht0 : -(1 / 128 : ℝ) ≤ theta) (ht1 : theta ≤ 0) :
    ghat 1 theta ≤ (65 / 4096 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hsq : theta ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := by nlinarith
  have hcube : theta ^ 3 ≤ 0 := by nlinarith [sq_nonneg theta]
  have hc : |theta / 64 + theta ^ 2 / 2| ≤ (1 / 8192 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg theta]
  have ha : |-(theta / 64 + theta ^ 2 / 2)| ≤
      65 / 4096 - ((1 + theta ^ 2) / 64 + theta ^ 3 / 3) := by
    rw [abs_neg]
    linarith
  have hb : |-(theta / 64 + theta ^ 2 / 2)| ≤ 65 / 4096 - (1 / 64 + theta) := by
    rw [abs_neg]
    linarith
  apply Matrix.le_iff.mpr
  convert posSemidef_two_of_diagonal ha hb using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

/-- Lower covariance bound at the next block, proved by a positive shifted polynomial. -/
theorem ghat_unit_next_lower {theta : ℝ} (ht : -(1 / 128 : ℝ) ≤ theta) :
    (125 / 2048 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ ghat 1 (theta + 1) := by
  let u := theta + 1 / 128
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ha : 0 < (1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048 := by
    have heq : (1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048 =
        u ^ 3 / 3 + 129 * u ^ 2 / 128 + 16637 * u / 16384 + 1859461 / 6291456 := by
      dsimp [u]
      ring
    rw [heq]
    positivity
  have hd : 0 <
      ((1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048) *
        (1 / 64 + (theta + 1) - 125 / 2048) -
      ((theta + 1) / 64 + (theta + 1) ^ 2 / 2) ^ 2 := by
    have heq :
        ((1 + (theta + 1) ^ 2) / 64 + (theta + 1) ^ 3 / 3 - 125 / 2048) *
          (1 / 64 + (theta + 1) - 125 / 2048) -
        ((theta + 1) / 64 + (theta + 1) ^ 2 / 2) ^ 2 =
        u ^ 4 / 12 + 1939 * u ^ 3 / 6144 + 116971 * u ^ 2 / 262144 +
          23512501 * u / 100663296 + 284017651 / 12884901888 := by dsimp [u]; ring
    rw [heq]
    positivity
  apply Matrix.le_iff.mpr
  convert (posDef_two_of_det ha hd).posSemidef using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.sub_apply, Matrix.smul_apply]
  all_goals ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
