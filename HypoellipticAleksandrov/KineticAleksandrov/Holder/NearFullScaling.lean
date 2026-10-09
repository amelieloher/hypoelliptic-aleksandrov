module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact volume scaling and the homogeneous cancellation in the near-full estimate -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open MeasureTheory

/-- Physical cylinder volume has the exact homogeneous coordinate dimension. -/
theorem volume_backwardCylinder_toReal {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) :
    (volume (backwardCylinder P₀ R)).toReal =
      R ^ (4 * d + 2) *
        (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal := by
  rw [← kineticAffine_image_unitCylinder P₀ hR, volume_kineticAffine_image P₀ hR,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hR _).le]

/-- The comparison radius, cutoff inverse-square factor and source volume powers cancel. -/
theorem near_full_radius_cancellation (d : ℕ) {R : ℝ} (hR : 0 < R) (p : ℝ) :
    R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
      (R ^ (4 * d + 2)) ^ (1 / p : ℝ) = 1 := by
  rw [← Real.rpow_natCast R 2, ← Real.rpow_neg hR.le,
    ← Real.rpow_natCast R (4 * d + 2), ← Real.rpow_mul hR.le,
    ← Real.rpow_add hR, ← Real.rpow_add hR]
  have heq : (2 - (4 * (d : ℝ) + 2) / p) + -(2 : ℝ) +
      ((4 * d + 2 : ℕ) : ℝ) * (1 / p) = 0 := by
    push_cast
    ring
  norm_num only [Nat.cast_ofNat]
  rw [heq, Real.rpow_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
