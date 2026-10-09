module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsScalar
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic

/-! # Uniform covariance estimates with the original ellipticity parameter -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped MatrixOrder

/-- Ellipticity is a scalar factor in the dimensionless covariance. -/
theorem ghat_smul (lam theta : ℝ) : ghat lam theta = lam • ghat 1 theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ghat, Matrix.smul_apply] <;> ring

/-- Nonnegative scalar multiplication preserves Loewner order. -/
theorem covariance_smul_le {A B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h : A ≤ B) (hc : 0 ≤ c) : c • A ≤ c • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp h).smul hc

/-- Upper covariance bound uniform in the ellipticity parameter. -/
theorem ghat_upper {lam theta : ℝ} (hlam : 0 < lam) (ht : |theta| ≤ 1) :
    ghat lam theta ≤ (2 * lam) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := covariance_smul_le (ghat_unit_upper ht) hlam.le
  simpa only [← ghat_smul, smul_smul, mul_comm lam 2] using h

/-- The next-block overlap factor is the source's exact dimensionless factor. -/
theorem ghat_overlap {lam theta : ℝ} (hlam : 0 < lam)
    (ht0 : -(1 / 128 : ℝ) ≤ theta) (ht1 : theta ≤ 0) :
    ghat lam theta ≤ (13 / 50 : ℝ) • ghat lam (theta + 1) := by
  have hupper := ghat_unit_cutoff_upper ht0 ht1
  have hlower := covariance_smul_le (ghat_unit_next_lower ht0)
    (by norm_num : (0 : ℝ) ≤ 13 / 50)
  have heq : (13 / 50 : ℝ) • ((125 / 2048 : ℝ) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (65 / 4096 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [smul_smul]
    norm_num
  rw [heq] at hlower
  have h := covariance_smul_le (hupper.trans hlower) hlam.le
  rw [ghat_smul lam theta, ghat_smul lam (theta + 1)]
  simpa only [smul_smul, mul_comm] using h

/-- Exact velocity diagonal entry of the inverse dimensionless covariance. -/
theorem ghat_inv_velocity (lam theta : ℝ) :
    (ghat lam theta)⁻¹ 1 1 =
      (lam / 64 * (1 + theta ^ 2) + lam * theta ^ 3 / 3) / (ghat lam theta).det := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp [ghat, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

/-- Inverse velocity bound, with exactly the source's constant. -/
theorem ghat_inv_velocity_le {lam theta : ℝ} (hlam : 0 < lam)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) : (ghat lam theta)⁻¹ 1 1 ≤ 128 / lam := by
  have hstrip : -(1 / 128 : ℝ) ≤ theta := by linarith
  have hdet := (posDef_ghat hlam hstrip).det_pos
  have hsq : theta ^ 2 ≤ theta := by nlinarith
  have hcube : 0 ≤ theta ^ 3 := pow_nonneg ht0 3
  have hfour : 0 ≤ theta ^ 4 := pow_nonneg ht0 4
  have hscalar : (1 + theta ^ 2) / 64 + theta ^ 3 / 3 ≤
      128 * (1 / 4096 + theta / 64 + theta ^ 3 / 192 + theta ^ 4 / 12) := by
    nlinarith
  rw [ghat_inv_velocity, div_le_div_iff₀ hdet hlam]
  rw [det_ghat]
  have h := mul_le_mul_of_nonneg_left hscalar (sq_nonneg lam)
  nlinarith

/-- The four source covariance properties, with Loewner order on scalar blocks. -/
theorem covariance_bounds (lam : ℝ) (hlam : 0 < lam) :
    (∀ theta : ℝ, -(1 / 128 : ℝ) ≤ theta → (ghat lam theta).PosDef) ∧
    (∀ theta : ℝ, |theta| ≤ 1 →
      ghat lam theta ≤ (2 * lam) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 → (ghat lam theta)⁻¹ 1 1 ≤ 128 / lam) ∧
    (∀ theta : ℝ, -(1 / 128 : ℝ) ≤ theta → theta ≤ 0 →
      ghat lam theta ≤ (13 / 50 : ℝ) • ghat lam (theta + 1)) :=
  ⟨fun _ ht => posDef_ghat hlam ht, fun _ ht => ghat_upper hlam ht,
    fun _ ht0 ht1 => ghat_inv_velocity_le hlam ht0 ht1,
    fun _ ht0 ht1 => ghat_overlap hlam ht0 ht1⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
