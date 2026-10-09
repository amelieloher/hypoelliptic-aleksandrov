module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierError

/-! # Quantitative R⁻¹ removal errors for sublinear regularized barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- The actual cutoff error vanishes outside the same physical rectangle. -/
theorem barrierRectError_zero_outside (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (Y R : ℝ) (z : Z)
    (hz : 2 < |(z.1 - Y) / R ^ 3| ∨ 2 < |z.2 / R|) :
    barrierRectError a f Y R z = 0 := by
  rcases hz with hx | hv
  · obtain ⟨h0, h1, _⟩ := barrierCutoff_zero_jets hx
    simp only [barrierRectError, h0, h1, zero_div, mul_zero, zero_mul, add_zero]
  · obtain ⟨h0, h1, h2⟩ := barrierCutoff_zero_jets hv
    simp only [barrierRectError, h0, h1, h2, zero_div, mul_zero, zero_mul, add_zero]

/-- The three actual errors have an explicit uniform inverse-radius bound.
Only the coefficient value, the coordinate modulus and the actual first velocity jet enter. -/
theorem barrierRectError_quantitative (a : ℝ → ℝ → ℝ) (f : Z → ℝ)
    (Lam alpha D Bv D1 D2 Y R : ℝ)
    (hLam : 0 ≤ Lam) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hD : 0 ≤ D) (hBv : 0 ≤ Bv) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hm : ∀ z w : Z, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha))
    (hbv : ∀ z : Z, |deriv (fun v => f (z.1, v)) z.2| ≤ Bv)
    (hb1 : ∀ x, |deriv barrierCutoff x| ≤ D1)
    (hb2 : ∀ x, |deriv (deriv barrierCutoff) x| ≤ D2)
    (hR : 1 ≤ R) (z : Z) (haz : 0 ≤ a z.1 z.2) (haL : a z.1 z.2 ≤ Lam) :
    |barrierRectError a f Y R z| ≤
      ((2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) + 2 * Lam * D1 * Bv) / R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hC : 0 ≤ (2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) +
      2 * Lam * D1 * Bv := by positivity
  by_cases hx : |(z.1 - Y) / R ^ 3| ≤ 2
  swap
  · rw [barrierRectError_zero_outside a f Y R z (Or.inl (lt_of_not_ge hx)), abs_zero]
    exact div_nonneg hC hR0.le
  by_cases hv : |z.2 / R| ≤ 2
  swap
  · rw [barrierRectError_zero_outside a f Y R z (Or.inr (lt_of_not_ge hv)), abs_zero]
    exact div_nonneg hC hR0.le
  have hxp : |z.1 - Y| ≤ 2 * R ^ 3 := (div_le_iff₀ (pow_pos hR0 3)).mp
    (by simpa only [abs_div, abs_of_pos (pow_pos hR0 3)] using hx)
  have hvp : |z.2| ≤ 2 * R := (div_le_iff₀ hR0).mp
    (by simpa only [abs_div, abs_of_pos hR0] using hv)
  let B := |f (Y, 0)| + 4 * D
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hfg := barrier_rectangle_growth f alpha D ha ha1 hD hm Y R hR z hxp hvp
  have hχ (x : ℝ) : |barrierCutoff x| ≤ 1 := by
    rw [abs_of_nonneg (barrierCutoff_bounds x).1]
    exact (barrierCutoff_bounds x).2
  have hdx : |deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3| ≤ D1 / R ^ 3 := by
    rw [abs_div, abs_of_pos (pow_pos hR0 3)]
    exact div_le_div_of_nonneg_right (hb1 _) (pow_nonneg hR0.le 3)
  have hdv : |deriv barrierCutoff (z.2 / R) / R| ≤ D1 / R := by
    rw [abs_div, abs_of_pos hR0]
    exact div_le_div_of_nonneg_right (hb1 _) hR0.le
  have hdvv : |deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2| ≤ D2 / R ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hR0 2)]
    exact div_le_div_of_nonneg_right (hb2 _) (pow_nonneg hR0.le 2)
  have hh := cutoff_error_abs_le (a z.1 z.2) Lam z.2
    (barrierCutoff ((z.1 - Y) / R ^ 3)) (barrierCutoff (z.2 / R))
    (deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3)
    (deriv barrierCutoff (z.2 / R) / R) (deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2)
    (f z) (deriv (fun v => f (z.1, v)) z.2) (D1 / R ^ 3) (D1 / R) (D2 / R ^ 2)
    (B * R) Bv haz haL (hχ _) (hχ _) hdx hdv hdvv hfg (hbv z)
  apply hh.trans
  calc
    _ ≤ (2 * R) * (D1 / R ^ 3) * (B * R) + Lam * (D2 / R ^ 2) * (B * R) +
        2 * Lam * (D1 / R) * Bv := by gcongr
    _ = _ := by dsimp only [B]; field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
