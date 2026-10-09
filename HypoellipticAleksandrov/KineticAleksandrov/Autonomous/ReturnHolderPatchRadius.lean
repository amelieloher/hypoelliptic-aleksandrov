module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # The quantitative positive-neighbourhood radius from a Holder modulus -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- A numerical radius factor making the Holder error at most half the positive height. -/
def returnHolderRadiusFactor (alpha D : ℝ) : ℝ := (1 / (2 * (D + 1))) ^ (1 / alpha)

/-- The fixed radius factor is positive and at most one. -/
theorem returnHolderRadiusFactor_bounds (alpha D : ℝ) (ha : 0 < alpha) (hD : 0 < D) :
    0 < returnHolderRadiusFactor alpha D ∧ returnHolderRadiusFactor alpha D ≤ 1 := by
  have hb : 0 < 1 / (2 * (D + 1)) := by positivity
  have hb1 : 1 / (2 * (D + 1)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * (D + 1))).mpr
    linarith
  exact ⟨Real.rpow_pos_of_pos hb _, Real.rpow_le_one hb.le hb1 (by positivity)⟩

/-- A value-relative radius makes the absolute modulus smaller than half that value. -/
theorem return_holder_radius (alpha D h value M : ℝ)
    (ha : 0 < alpha) (hD : 0 < D) (hh : 0 < h)
    (hvalue : 0 < value) (hM : 0 < M) (hvalueM : value ≤ M) :
    let ell := returnHolderRadiusFactor alpha D * h * (value / M) ^ (1 / alpha)
    0 < ell ∧ ell ≤ h ∧ D * M * (ell / h) ^ alpha ≤ value / 2 := by
  let δ := returnHolderRadiusFactor alpha D
  have hδ := returnHolderRadiusFactor_bounds alpha D ha hD
  have hratio : 0 < value / M := div_pos hvalue hM
  have hratio1 : value / M ≤ 1 := (div_le_one hM).mpr hvalueM
  have hroot : 0 < (value / M) ^ (1 / alpha) := Real.rpow_pos_of_pos hratio _
  have hroot1 : (value / M) ^ (1 / alpha) ≤ 1 :=
    Real.rpow_le_one hratio.le hratio1 (by positivity)
  have hδpower : δ ^ alpha = 1 / (2 * (D + 1)) := by
    dsimp [δ, returnHolderRadiusFactor]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 / (2 * (D + 1)))]
    rw [one_div_mul_cancel ha.ne', Real.rpow_one]
  have hpower : (δ * h * (value / M) ^ (1 / alpha) / h) ^ alpha =
      (1 / (2 * (D + 1))) * (value / M) := by
    have he : δ * h * (value / M) ^ (1 / alpha) / h =
        δ * (value / M) ^ (1 / alpha) := by field_simp
    rw [he, Real.mul_rpow hδ.1.le hroot.le, hδpower,
      ← Real.rpow_mul hratio.le, one_div_mul_cancel ha.ne', Real.rpow_one]
  refine ⟨mul_pos (mul_pos hδ.1 hh) hroot, ?_, ?_⟩
  · have hprod := mul_le_mul hδ.2 hroot1 hroot.le zero_le_one
    have he := mul_le_mul_of_nonneg_right hprod hh.le
    dsimp only [δ] at *
    nlinarith
  · change D * M * (δ * h * (value / M) ^ (1 / alpha) / h) ^ alpha ≤ value / 2
    rw [hpower]
    have he : D * M * (1 / (2 * (D + 1)) * (value / M)) =
        (D / (2 * (D + 1))) * value := by field_simp
    rw [he]
    have hcoef : D / (2 * (D + 1)) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (D + 1))).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef hvalue.le).trans_eq (by ring)

/-- The height-relative radius produces the source nonlinear height expression. -/
theorem return_holder_height_factor (alpha beta c δ h value M : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 ≤ h) (hvalue : 0 < value) (hM : 0 < M) :
    c * (δ * h * (value / M) ^ (1 / alpha)) ^ beta * (value / 2) =
      (c * δ ^ beta / 2) * h ^ beta * value ^ (1 + beta / alpha) * M ^ (-beta / alpha) := by
  rw [Real.mul_rpow (mul_nonneg hδ hh) (Real.rpow_nonneg (div_nonneg hvalue.le hM.le) _),
    Real.mul_rpow hδ hh, ← Real.rpow_mul (div_nonneg hvalue.le hM.le)]
  have he : 1 / alpha * beta = beta / alpha := by ring
  rw [he, Real.div_rpow hvalue.le hM.le, Real.rpow_add hvalue,
    Real.rpow_one, neg_div, Real.rpow_neg hM.le]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
