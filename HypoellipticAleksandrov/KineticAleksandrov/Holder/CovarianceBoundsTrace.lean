module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovariancePhysical
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! # Velocity block trace bound in native dimension -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Exact rescaling of the inverse velocity block. -/
theorem gramian_inv_velocity_scaling {lam h s : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ s) :
    (gramian lam h s)⁻¹ 1 1 = (ghat lam (s / h))⁻¹ 1 1 / h := by
  have hstrip : -(1 / 128 : ℝ) ≤ s / h := by
    apply (le_div_iff₀ hh).mpr
    linarith
  have hd := (posDef_ghat hlam hstrip).det_pos.ne'
  have hscale : covarianceDet lam h s = h ^ 4 * (ghat lam (s / h)).det := by
    rw [det_ghat]
    unfold covarianceDet covarianceXX covarianceVV covarianceXV
    field_simp
    ring
  have ha : covarianceXX lam h s =
      h ^ 3 * (lam / 64 * (1 + (s / h) ^ 2) + lam * (s / h) ^ 3 / 3) := by
    unfold covarianceXX
    field_simp
  rw [gramian_inv_blocks lam hh, ghat_inv_velocity]
  simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hscale, ha]
  field_simp

/-- Native velocity block trace bound, with the original dimension and physical scale. -/
theorem gramian_velocity_trace_le (d : ℕ) {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs0 : 0 ≤ s) (hs1 : s ≤ h) :
    Matrix.trace (((gramian lam h s)⁻¹ 1 1) • (1 : PDE.Mat d)) ≤
      (128 * (d : ℝ) / lam) / h := by
  have ht0 : 0 ≤ s / h := div_nonneg hs0 hh.le
  have ht1 : s / h ≤ 1 := (div_le_one hh).mpr hs1
  have hs : -(h / 128) ≤ s := by linarith
  rw [gramian_inv_velocity_scaling hlam hh hs, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  have hi := div_le_div_of_nonneg_right (ghat_inv_velocity_le hlam ht0 ht1) hh.le
  have hm := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  convert hm using 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
