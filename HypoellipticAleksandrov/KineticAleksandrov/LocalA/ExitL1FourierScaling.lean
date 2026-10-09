module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1FourierMoments
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Raw position-frequency scaling before any probability normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory

/-- The structural stretched-exponential moment at unit spatial scale. -/
def exitFrequencyMoment {d : ℕ} (c : ℝ) (j : ℕ) : ℝ :=
  ∫ ξ : PDE.Vec d, ‖ξ‖ ^ j * Real.exp (-c * ‖ξ‖ ^ (1 / 3 : ℝ))

/-- Unit-scale frequency moments are nonnegative. -/
theorem exitFrequencyMoment_nonneg {d : ℕ} (c : ℝ) (j : ℕ) :
    0 ≤ exitFrequencyMoment (d := d) c j :=
  integral_nonneg (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg ξ) j) (Real.exp_pos _).le)

/-- Frequency dilation gives the raw dimension-plus-derivative scaling factor. -/
theorem exitFrequencyMoment_scaling {d : ℕ} (c : ℝ) (j : ℕ) {R : ℝ} (hR : 0 < R) :
    (∫ ξ : PDE.Vec d, ‖ξ‖ ^ j *
      Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ))) =
      ((R ^ 3) ^ (d + j))⁻¹ * exitFrequencyMoment (d := d) c j := by
  let f : PDE.Vec d → ℝ := fun ξ =>
    ‖ξ‖ ^ j * Real.exp (-c * ‖ξ‖ ^ (1 / 3 : ℝ))
  have hn : R ^ 3 ≠ 0 := (pow_pos hR 3).ne'
  have heq : (fun ξ : PDE.Vec d => ‖ξ‖ ^ j *
      Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ))) =
      fun ξ => ((R ^ 3) ^ j)⁻¹ * f (R ^ 3 • ξ) := by
    funext ξ
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR 3), mul_pow]
    field_simp
  rw [heq, integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume f (R ^ 3)
      (hR := (pow_pos hR 3).le)]
  have hdim : Module.finrank ℝ (PDE.Vec d) = d := by
    simpa only [Fintype.card_fin] using
      (Module.finrank_fintype_fun_eq_card ℝ (η := Fin d))
  rw [hdim]
  change ((R ^ 3) ^ j)⁻¹ * (((R ^ 3) ^ d)⁻¹ * exitFrequencyMoment c j) = _
  rw [pow_add, mul_inv_rev, mul_assoc]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
