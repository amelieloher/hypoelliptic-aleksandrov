module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor
import Mathlib.Tactic

/-!
# Gamma moments of the positive-axis expansion

This module evaluates the integral Taylor polynomial with the exact rising-factorial
coefficients of the source expansion.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Finite positive-axis U expansion in inverse powers of the argument. -/
def uExpansion (a b : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  z ^ (-a) * ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * z⁻¹ ^ n

/-- Binomial coefficients written with the signed rising factorial. -/
theorem choose_eq_signed_poch (q : ℝ) (n : ℕ) :
    Ring.choose q n = (-1 : ℝ) ^ n * poch (-q) n / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer, poch,
    ascPochhammer_eval_neg_eq_descPochhammer, smul_eq_mul]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow]
  rw [← mul_assoc, hs]
  ring

/-- Gamma recurrence at every nonnegative integer shift of a positive shape. -/
theorem Gamma_add_nat_eq_poch (a : Pos) (n : ℕ) :
    Real.Gamma (a.1 + n) = Real.Gamma a.1 * poch a.1 n := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, poch_zero, mul_one]
  | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc,
        Real.Gamma_add_one (ne_of_gt (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n))),
        ih, poch_succ]
      ring

/-- Evaluation of a scaled real Gamma kernel. -/
theorem integral_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a - 1)) =
      z ^ (-a) * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hz
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_comm] using h

/-- The nth Gamma moment has precisely the source rising-factorial coefficient. -/
theorem integral_gammaKernel_moment (a : Pos) (z : ℝ) (hz : 0 < z) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) =
      Real.Gamma a.1 * poch a.1 n * z ^ (-a.1) * z⁻¹ ^ n := by
  have heq : (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 + (n : ℝ) - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [show a.1 + (n : ℝ) - 1 = (a.1 - 1) + (n : ℝ) by ring,
      Real.rpow_add ht, Real.rpow_natCast]
    ring
  rw [heq, integral_gammaKernel _ z
    (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n)) hz, Gamma_add_nat_eq_poch]
  rw [neg_add, Real.rpow_add hz]
  simp only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  ring

/-- Integrability of each Taylor moment before finite summation. -/
theorem integrableOn_gammaKernel_moment (a : Pos) (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n)
      (Ioi 0) volume := by
  apply IntegrableOn.congr_fun
    (integrableOn_gammaKernel (a.1 + n) z
      (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n)) hz) _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show a.1 + (n : ℝ) - 1 = (a.1 - 1) + (n : ℝ) by ring,
    Real.rpow_add ht, Real.rpow_natCast]
  ring

/-- Integrability of the complete finite Taylor polynomial against the Gamma kernel. -/
theorem integrableOn_gammaKernel_powerTaylor (a : Pos) (q z : ℝ) (hz : 0 < z) (N : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) * powerTaylor q N t)
      (Ioi 0) volume := by
  have h := integrable_finsetSum (Finset.range N)
    (fun n _ => (integrableOn_gammaKernel_moment a z hz n).const_mul (Ring.choose q n))
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t _
  simp only [powerTaylor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The integral of the finite binomial polynomial equals the normalized expansion. -/
theorem integral_powerTaylor (a : Pos) (b z : ℝ) (hz : 0 < z) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) *
      powerTaylor (b - a.1 - 1) N t) = Real.Gamma a.1 * uExpansion a.1 b N z := by
  have hsum : (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) *
      powerTaylor (b - a.1 - 1) N t) =
      ∑ n ∈ Finset.range N, Ring.choose (b - a.1 - 1) n *
        (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) := by
    simp only [powerTaylor, Finset.mul_sum]
    have heq : (fun t : ℝ => ∑ n ∈ Finset.range N,
        Real.exp (-(z * t)) * t ^ (a.1 - 1) * (Ring.choose (b - a.1 - 1) n * t ^ n)) =
        (fun t => ∑ n ∈ Finset.range N, Ring.choose (b - a.1 - 1) n *
          (Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n)) := by
      funext t
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [heq, integral_finsetSum]
    · simp only [integral_const_mul]
    · intro n _
      exact (integrableOn_gammaKernel_moment a z hz n).const_mul _
  rw [hsum]
  simp only [uExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_gammaKernel_moment a z hz n, choose_eq_signed_poch,
    show -(b - a.1 - 1) = a.1 - b + 1 by ring]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
