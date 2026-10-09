module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.EulerIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquationContiguous
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebraic expansion coefficients for Kummer M on the negative real axis

The finite polynomial and the ordinary derivative jets use the literal source normalization.
-/

@[expose] public noncomputable section

open scoped NNReal ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- The finite negative-axis expansion with its Gamma normalization. -/
def mExpansion (a b : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  Real.Gamma b / Real.Gamma (b - a) * Real.rpow X (-a) *
    ∑ n ∈ Finset.range N, poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * X⁻¹ ^ n

/-- Iterated ordinary derivatives, including the zeroth derivative. -/
def jet (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[j]) f

/-- The polynomial arising from the Taylor expansion of the Euler weight. -/
def betaPolynomial (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch q n / (n.factorial : ℝ) * t ^ n

private theorem multichoose_eq_poch (q : ℝ) (n : ℕ) :
    Ring.multichoose q n = poch q n / (n.factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
  rw [mul_comm, ← nsmul_eq_mul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval]
  rfl

private theorem betaPolynomial_eq_partialSum (q : ℝ) (N : ℕ) (t : ℝ) :
    betaPolynomial q N t =
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n => poch q n / (n.factorial : ℝ))).partialSum N t := by
  simp only [betaPolynomial, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- The singular Beta factor has its exact rising-factorial Taylor series near zero. -/
theorem betaFactor_hasFPowerSeries (q : ℝ) :
    HasFPowerSeriesOnBall (fun t : ℝ => 1 / (1 - t) ^ q)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => poch q n / (n.factorial : ℝ)))
      0 1 := by
  convert Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero q using 1
  ext n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, one_pow, mul_one,
    ← Ring.multichoose_eq, multichoose_eq_poch]

/-- A uniform Taylor remainder on the first half of the Euler interval. -/
theorem betaFactor_remainder_bound (q : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      |(1 - t) ^ (-q) - betaPolynomial q N t| ≤ C * t ^ N := by
  have hl : ((3 / 4 : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    norm_num
  obtain ⟨r, hr, C, hC, hb⟩ := (betaFactor_hasFPowerSeries q)
    |>.uniform_geometric_approx' hl
  refine ⟨C * (r / (3 / 4)) ^ N, mul_pos hC (pow_pos (div_pos hr.1 (by norm_num)) _), ?_⟩
  intro t ht ht1
  have htball : t ∈ Metric.ball (0 : ℝ) (3 / 4 : ℝ≥0) := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
    norm_num
    linarith only [ht1]
  have hh := hb t htball N
  rw [zero_add, one_div, ← Real.rpow_neg (sub_nonneg.mpr (by linarith only [ht1])),
    ← betaPolynomial_eq_partialSum] at hh
  simpa only [NNReal.coe_div, NNReal.coe_ofNat, Real.norm_eq_abs, abs_of_nonneg ht,
    mul_pow, div_pow, mul_assoc,
    mul_div_assoc, div_mul_eq_mul_div] using hh

/-- The Gamma-normalized coefficient of each negative-axis power. -/
def expansionCoeff (a b : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma b / Real.Gamma (b - a) * poch a n * poch (a - b + 1) n /
    (n.factorial : ℝ)

/-- Writing the finite expansion as individual real powers. -/
theorem mExpansion_eq_sum (a b : ℝ) (N : ℕ) (X : ℝ) (hX : 0 < X) :
    mExpansion a b N X =
      ∑ n ∈ Finset.range N, expansionCoeff a b n * Real.rpow X (-(a + n)) := by
  simp only [mExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hx : Real.rpow X (-(a + n)) = Real.rpow X (-a) * X⁻¹ ^ n := by
    change X ^ (-(a + (n : ℝ))) = X ^ (-a) * X⁻¹ ^ n
    rw [show -(a + (n : ℝ)) = -a + -(n : ℝ) by ring,
      Real.rpow_add hX, Real.rpow_neg hX.le (n : ℝ), Real.rpow_natCast, inv_pow]
  rw [hx]
  unfold expansionCoeff
  change Real.Gamma b / Real.Gamma (b - a) * Real.rpow X (-a) *
    (poch a n * poch (a - b + 1) n / (n.factorial : ℝ) * X⁻¹ ^ n) =
      (Real.Gamma b / Real.Gamma (b - a) * poch a n * poch (a - b + 1) n /
        (n.factorial : ℝ)) * (Real.rpow X (-a) * X⁻¹ ^ n)
  ring

/-- Raising both parameters matches differentiation of an expansion coefficient. -/
theorem expansionCoeff_deriv (a : ℝ) (b : Pos) (n : ℕ) :
    -(a + n) * expansionCoeff a b.1 n =
      -(a / b.1) * expansionCoeff (a + 1) (b.1 + 1) n := by
  have hb := ne_of_gt b.2
  rw [expansionCoeff, expansionCoeff, Real.Gamma_add_one hb,
    show b.1 + 1 - (a + 1) = b.1 - a by ring,
    show a + 1 - (b.1 + 1) + 1 = a - b.1 + 1 by ring]
  have hs := poch_shift a n
  have hsm := congrArg (fun x : ℝ =>
    -Real.Gamma b.1 * poch (a - b.1 + 1) n * x /
      (Real.Gamma (b.1 - a) * (n.factorial : ℝ))) hs
  field_simp at hsm ⊢
  nlinarith only [hsm]

/-- Derivative of the finite expansion, preserving its truncation order. -/
theorem hasDerivAt_mExpansion (a : ℝ) (b : Pos) (N : ℕ) (X : ℝ) (hX : 0 < X) :
    HasDerivAt (mExpansion a b.1 N)
      (-(a / b.1) * mExpansion (a + 1) (b.1 + 1) N X) X := by
  have hd : HasDerivAt
      (fun Y : ℝ => ∑ n ∈ Finset.range N,
        expansionCoeff a b.1 n * Real.rpow Y (-(a + n)))
      (∑ n ∈ Finset.range N, expansionCoeff a b.1 n *
        (-(a + n) * Real.rpow X (-(a + n) - 1))) X := by
    apply HasDerivAt.fun_sum
    intro n _
    exact (Real.hasDerivAt_rpow_const (Or.inl hX.ne')).const_mul _
  have he : (fun Y : ℝ => ∑ n ∈ Finset.range N,
      expansionCoeff a b.1 n * Real.rpow Y (-(a + n))) =ᶠ[nhds X] mExpansion a b.1 N := by
    filter_upwards [eventually_gt_nhds hX] with Y hY
    exact (mExpansion_eq_sum a b.1 N Y hY).symm
  apply (hd.congr_of_eventuallyEq he.symm).congr_deriv
  rw [mExpansion_eq_sum (a + 1) (b.1 + 1) N X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [show -(a + (n : ℝ)) - 1 = -(a + 1 + n) by ring]
  rw [← mul_assoc, mul_comm (expansionCoeff a b.1 n), expansionCoeff_deriv]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
