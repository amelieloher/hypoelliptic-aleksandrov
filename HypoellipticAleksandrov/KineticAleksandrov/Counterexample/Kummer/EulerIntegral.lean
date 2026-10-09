module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Euler integral for the confluent hypergeometric function

Beta weights and their moments, on the real unit interval.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set

/-- The real Beta weight. -/
def betaWeight (a c t : ℝ) : ℝ := t ^ (a - 1) * (1 - t) ^ (c - 1)

/-- The real Beta weight agrees with the complex integral kernel on the unit interval. -/
theorem betaWeight_ofReal (a c t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (betaWeight a c t : ℂ) = (t : ℂ) ^ ((a : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((c : ℂ) - 1) := by
  rw [betaWeight, Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
    Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

/-- The Beta weight is integrable for positive endpoint parameters. -/
theorem intervalIntegrable_betaWeight (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntervalIntegrable (betaWeight a c) volume 0 1 := by
  have hi := Complex.betaIntegral_convergent (by exact ha : 0 < (a : ℂ).re)
    (by exact hc : 0 < (c : ℂ).re)
  have he : IntervalIntegrable (fun t => (betaWeight a c t : ℂ)) volume 0 1 :=
    hi.congr (fun t ht => by
      rw [uIoc_of_le (by norm_num)] at ht
      exact (betaWeight_ofReal a c t ⟨ht.1.le, ht.2⟩).symm)
  exact ⟨Integrable.iff_ofReal.mpr he.1, Integrable.iff_ofReal.mpr he.2⟩

/-- Evaluation of the real Beta integral. -/
theorem integral_betaWeight (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1, betaWeight a c t) =
      Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t in (0 : ℝ)..1, (betaWeight a c t : ℂ)) =
      Complex.betaIntegral (a : ℂ) (c : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact betaWeight_ofReal a c t ht
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (c : ℂ) ha hc]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.Gamma_ofReal]

/-- Gamma moments in rising-factorial notation. -/
theorem Gamma_add_nat (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) = poch a n * Real.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : a + n ≠ 0 := ne_of_gt
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n))
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one hn, ih, poch_succ]
    ring

/-- Multiplication by a monomial shifts the Beta parameter. -/
theorem betaWeight_mul_pow (a c t : ℝ) (ht : 0 < t) (n : ℕ) :
    betaWeight a c t * t ^ n = betaWeight (a + n) c t := by
  rw [betaWeight, betaWeight, ← Real.rpow_natCast]
  rw [mul_right_comm, ← Real.rpow_add ht]
  congr 2
  ring

/-- Beta moments of the Euler weight. -/
theorem integral_betaWeight_mul_pow (a : ℝ) (b : Pos) (ha : 0 < a)
    (hab : a < b.1) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, betaWeight a (b.1 - a) t * t ^ n) =
      poch a n * Real.Gamma a * Real.Gamma (b.1 - a) /
        (poch b.1 n * Real.Gamma b.1) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    (fun t ht => betaWeight_mul_pow a (b.1 - a) t ht.1 n)]
  rw [integral_betaWeight (a + n) (b.1 - a)
    (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) (sub_pos.mpr hab)]
  have he : a + n + (b.1 - a) = b.1 + n := by ring
  rw [he, Gamma_add_nat a ha n, Gamma_add_nat b.1 b.2 n]

/-- Euler's exponential series in real notation. -/
theorem hasSum_exp_real (z : ℝ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- Nonnegativity of the Beta weight on the unit interval. -/
theorem betaWeight_nonneg (a c t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ betaWeight a c t :=
  mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

private theorem euler_term_integrable (a c z : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) : IntervalIntegrable
      (fun t => betaWeight a c t * ((z * t) ^ n / (n.factorial : ℝ))) volume 0 1 := by
  exact (intervalIntegrable_betaWeight a c ha hc).mul_continuousOn (by fun_prop)

private theorem euler_term_bound (a c z t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ‖betaWeight a c t * ((z * t) ^ n / (n.factorial : ℝ))‖ ≤
      betaWeight a c t * (|z| ^ n / (n.factorial : ℝ)) := by
  have hw := betaWeight_nonneg a c t ht
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs,
    abs_div, abs_pow, abs_mul, abs_of_nonneg ht.1, abs_of_pos hf, mul_pow, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hw
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hf.le
  exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg z) n) (pow_le_one₀ ht.1 ht.2)

/-- Dominated integration of the exponential series against a Beta weight. -/
theorem hasSum_euler_integral (a c z : ℝ) (ha : 0 < a) (hc : 0 < c) :
    HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..1,
      betaWeight a c t * ((z * t) ^ n / (n.factorial : ℝ)))
      (∫ t in (0 : ℝ)..1, betaWeight a c t * Real.exp (z * t)) := by
  have hb (t : ℝ) : HasSum
      (fun n : ℕ => betaWeight a c t * (|z| ^ n / (n.factorial : ℝ)))
      (betaWeight a c t * Real.exp |z|) :=
    (hasSum_exp_real |z|).mul_left (betaWeight a c t)
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n t => betaWeight a c t * (|z| ^ n / (n.factorial : ℝ)))
  · intro n
    exact (euler_term_integrable a c z ha hc n).def'.aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le (by norm_num)] at ht
      exact euler_term_bound a c z t ⟨ht.1.le, ht.2⟩ n)
  · exact Filter.Eventually.of_forall (fun t _ => (hb t).summable)
  · simp only [(hb _).tsum_eq]
    exact (intervalIntegrable_betaWeight a c ha hc).mul_const (Real.exp |z|)
  · exact Filter.Eventually.of_forall
      (fun t _ => (hasSum_exp_real (z * t)).mul_left (betaWeight a c t))

private theorem integral_euler_term (a : ℝ) (b : Pos) (ha : 0 < a)
    (hab : a < b.1) (z : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      betaWeight a (b.1 - a) t * ((z * t) ^ n / (n.factorial : ℝ))) =
      (Real.Gamma a * Real.Gamma (b.1 - a) / Real.Gamma b.1) *
        (coeff a b n * z ^ n) := by
  have he (t : ℝ) :
      betaWeight a (b.1 - a) t * ((z * t) ^ n / (n.factorial : ℝ)) =
        (z ^ n / (n.factorial : ℝ)) * (betaWeight a (b.1 - a) t * t ^ n) := by
    rw [mul_pow]
    ring
  simp only [he, intervalIntegral.integral_const_mul]
  rw [integral_betaWeight_mul_pow a b ha hab n, coeff]
  ring

/-- Euler's integral representation of the literal power series for positive parameters. -/
theorem M_euler_integral (a : ℝ) (b : Pos) (ha : 0 < a) (hab : a < b.1) (z : ℝ) :
    M a b z = Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)) *
      ∫ t in (0 : ℝ)..1, Real.exp (z * t) * betaWeight a (b.1 - a) t := by
  have hs := hasSum_euler_integral a (b.1 - a) z ha (sub_pos.mpr hab)
  simp only [integral_euler_term a b ha hab z] at hs
  have hm := (hasSum_M a b z).mul_left
    (Real.Gamma a * Real.Gamma (b.1 - a) / Real.Gamma b.1)
  have he := hm.unique hs
  have haG := ne_of_gt (Real.Gamma_pos_of_pos ha)
  have hcG := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
  have hbG := ne_of_gt (Real.Gamma_pos_of_pos b.2)
  rw [show (∫ t in (0 : ℝ)..1, Real.exp (z * t) * betaWeight a (b.1 - a) t) =
    (∫ t in (0 : ℝ)..1, betaWeight a (b.1 - a) t * Real.exp (z * t)) by
      apply intervalIntegral.integral_congr; intro t _; ring, ← he]
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
