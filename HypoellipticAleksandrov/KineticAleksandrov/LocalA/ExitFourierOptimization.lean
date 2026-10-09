module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A strictly interior optimizing time step at the maximal short horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA

/-- Squaring the dimensionless frequency cube root gives the kinetic frequency scale. -/
theorem exitFrequency_square {R n : ℝ} (hR : 0 ≤ R) (hn : 0 ≤ n) :
    ((R ^ 3 * n) ^ (1 / 3 : ℝ)) ^ 2 = R ^ 2 * n ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast (mul_nonneg (pow_nonneg hR _) hn)]
  norm_num only
  rw [Real.mul_rpow (pow_nonneg hR _) hn, ← Real.rpow_natCast_mul hR]
  norm_num

/-- High frequencies have a positive optimizing step strictly below the maximal horizon.
The factor sixteen treats equality at dimensionless frequency one without a limiting step. -/
theorem exitFrequency_optimizing_step {R n : ℝ} (hR : 0 < R) (hn : 0 ≤ n)
    (hhigh : 1 ≤ R ^ 3 * n) :
    let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
    let h := R ^ 2 / (16 * y)
    1 ≤ y ∧ 0 < h ∧ h < R ^ 2 / 8 ∧
      R ^ 2 / h = 16 * y ∧ h * n ^ (2 / 3 : ℝ) = y / 16 := by
  let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
  have hy : 1 ≤ y := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow zero_le_one hhigh (by norm_num : 0 ≤ (1 / 3 : ℝ))
  have hyp : 0 < y := zero_lt_one.trans_le hy
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hh : R ^ 2 / (16 * y) ≤ R ^ 2 / 16 := by
    apply div_le_div_of_nonneg_left hR2.le (by norm_num)
    nlinarith only [hy]
  refine ⟨hy, div_pos hR2 (mul_pos (by norm_num) hyp),
    hh.trans_lt (by linarith only [hR2]), ?_, ?_⟩
  · field_simp
  · have hs := exitFrequency_square hR.le hn
    change y ^ 2 = R ^ 2 * n ^ (2 / 3 : ℝ) at hs
    calc
      R ^ 2 / (16 * y) * n ^ (2 / 3 : ℝ) =
          (R ^ 2 * n ^ (2 / 3 : ℝ)) / (16 * y) := by ring
      _ = y ^ 2 / (16 * y) := by rw [← hs]
      _ = y / 16 := by field_simp

/-- A pair of exponential bounds collapses at a step with the two exact frequency identities. -/
theorem exitFrequency_exponential_pair {C c y h R n : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hy : 0 ≤ y)
    (hfirst : R ^ 2 / h = 16 * y) (hsecond : h * n ^ (2 / 3 : ℝ) = y / 16) :
    C * (Real.exp (-c * R ^ 2 / h) + Real.exp (-c * h * n ^ (2 / 3 : ℝ))) ≤
      2 * C * Real.exp (-(c / 16) * y) := by
  have h1 : -c * R ^ 2 / h = -c * (16 * y) := by rw [← hfirst]; ring
  have h2 : -c * h * n ^ (2 / 3 : ℝ) = -c * (y / 16) := by rw [← hsecond]; ring
  have ha : Real.exp (-c * (16 * y)) ≤ Real.exp (-(c / 16) * y) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hc hy]
  have hb : Real.exp (-c * (y / 16)) = Real.exp (-(c / 16) * y) := by congr 1; ring
  rw [h1, h2, hb]
  calc
    _ ≤ C * (Real.exp (-(c / 16) * y) + Real.exp (-(c / 16) * y)) :=
      mul_le_mul_of_nonneg_left (add_le_add ha le_rfl) hC
    _ = _ := by ring

/-- Unit variation supplies the same exponential estimate throughout the low-frequency range. -/
theorem exitFrequency_low_bound {A c y : ℝ} (hA : 1 ≤ A) (hc : 0 ≤ c) (hy : y ≤ 1) :
    1 ≤ (A * Real.exp c) * Real.exp (-c * y) := by
  rw [mul_assoc, ← Real.exp_add]
  have hs : 0 ≤ c + -c * y := by
    have h := mul_nonneg hc (sub_nonneg.mpr hy)
    linarith only [h]
  calc
    1 ≤ Real.exp (c + -c * y) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hs
    _ ≤ A * Real.exp (c + -c * y) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
