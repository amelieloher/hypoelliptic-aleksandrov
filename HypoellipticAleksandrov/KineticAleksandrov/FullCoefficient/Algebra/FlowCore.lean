module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Algebraic core of the flow identities

The coefficient identity of the flow. Real-number
inequality: for `1 < q ≤ 4/3`, `r > 0`, and a nonnegative Cauchy-Schwarz triple
`(Γrr, Γrb, Γbb)`, the three terms with coefficients `q(q-1)`, `4(q-1)` and `2` dominate
`r^q Γbb`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

/-- Rewriting the powers of `r` through `s = r^(q-2)`. -/
theorem rpow_split {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r ^ (q - 1) = r ^ (q - 2) * r ∧ r ^ q = r ^ (q - 2) * r ^ 2 := by
  constructor
  · have := Real.rpow_add hr (q - 2) 1
    rw [Real.rpow_one] at this
    rw [← this]; ring_nf
  · have := Real.rpow_add hr (q - 2) 2
    rw [show (q - 2 + 2 : ℝ) = q by ring, Real.rpow_two] at this
    exact this

/-- The completed square: the quadratic form with coefficients `q(q-1)`, `4(q-1)`, `1`. -/
theorem quad_nonneg {q β r Γrr Γrb Γbb : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 4 / 3)
    (hΓrr : 0 ≤ Γrr) (hΓbb : 0 ≤ Γbb) (hcs : Γrb ^ 2 ≤ Γrr * Γbb) :
    0 ≤ q * (q - 1) * β ^ 2 * Γrr + 4 * (q - 1) * r * β * Γrb + r ^ 2 * Γbb := by
  have hq0 : 0 < q := by linarith
  have hq1' : 0 < q - 1 := by linarith
  rcases hΓrr.eq_or_lt with h0 | hpos
  · have : Γrb = 0 := by
      have : Γrb ^ 2 ≤ 0 := by rw [← h0] at hcs; simpa using hcs
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
    subst this
    rw [← h0]
    nlinarith [mul_nonneg (sq_nonneg r) hΓbb]
  · have key : Γrr * (q * (q - 1) * β ^ 2 * Γrr + 4 * (q - 1) * r * β * Γrb + r ^ 2 * Γbb)
        = (q - 1) / q * (q * Γrr * β + 2 * Γrb * r) ^ 2
          + r ^ 2 * (Γrr * Γbb - 4 * (q - 1) / q * Γrb ^ 2) := by
      field_simp
      ring
    have h2 : 0 ≤ Γrr * Γbb - 4 * (q - 1) / q * Γrb ^ 2 := by
      have hc : 4 * (q - 1) / q ≤ 1 := by
        rw [div_le_one hq0]; linarith
      have : 4 * (q - 1) / q * Γrb ^ 2 ≤ 1 * Γrb ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      linarith
    have h3 : 0 ≤ Γrr * (q * (q - 1) * β ^ 2 * Γrr + 4 * (q - 1) * r * β * Γrb + r ^ 2 * Γbb) := by
      rw [key]; positivity
    exact (mul_nonneg_iff_of_pos_left hpos).mp h3

/-- Core inequality of the coefficient identity. -/
theorem coef_core {q r β Γrr Γrb Γbb : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 4 / 3) (hr : 0 < r)
    (hΓrr : 0 ≤ Γrr) (hΓbb : 0 ≤ Γbb) (hcs : Γrb ^ 2 ≤ Γrr * Γbb) :
    r ^ q * Γbb ≤ 2 * (r ^ q * Γbb) + q * (q - 1) * r ^ (q - 2) * β ^ 2 * Γrr
      + 4 * (q - 1) * r ^ (q - 1) * β * Γrb := by
  obtain ⟨h1, h2⟩ := rpow_split hr q
  have hs : 0 < r ^ (q - 2) := Real.rpow_pos_of_pos hr _
  have := quad_nonneg (β := β) (r := r) hq1 hq2 hΓrr hΓbb hcs
  rw [h1, h2]
  nlinarith [mul_nonneg hs.le this]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
