module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Normalizing the exact quadratic weight in the source slab bound -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The quadratic weight gives a uniform constant after its exact radius cancellation. -/
theorem positionStart_slab_arithmetic (r C n F I : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hF : 0 ≤ F) (hI : 0 ≤ I)
    (h : 5 * r ^ 2 / 16 * n ≤ 9 * r ^ 2 / 16 * F + C * I) :
    n ≤ (9 / 5 + 16 * C / 5) * (F + r ^ (-2 : ℤ) * I) := by
  have hw : 0 < 5 * r ^ 2 / 16 := by positivity
  have he : 5 * r ^ 2 / 16 * (9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I) =
      9 * r ^ 2 / 16 * F + C * I := by
    rw [zpow_neg, zpow_ofNat]
    field_simp [hr.ne']
  have hn : n ≤ 9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I :=
    le_of_mul_le_mul_left (h.trans_eq he.symm) hw
  have hpos : 0 ≤ r ^ (-2 : ℤ) * I := mul_nonneg (zpow_nonneg hr.le _) hI
  calc
    n ≤ 9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I := hn
    _ ≤ (9 / 5 + 16 * C / 5) * F +
        (9 / 5 + 16 * C / 5) * (r ^ (-2 : ℤ) * I) := by
      rw [mul_assoc]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith only [hC]) hF)
        (mul_le_mul_of_nonneg_right (by linarith) hpos)
    _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
