module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsEuler
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Gamma-normalized algebraic expansion for positive first parameter

Euler's representation and its moment expansion give the literal Kummer normalization.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/-- The full Gamma polynomial equals the normalized algebraic expansion. -/
theorem gammaPolynomial_normalized (a : ℝ) (b : Pos) (N : ℕ) (X : ℝ)
    (ha : 0 < a) (hab : a < b.1) (hX : 0 < X) :
    Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)) *
      gammaPolynomial a (b.1 - a) N X = mExpansion a b.1 N X := by
  have hGa := ne_of_gt (Real.Gamma_pos_of_pos ha)
  have hGc := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
  simp only [gammaPolynomial, mExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Gamma_add_nat a ha n]
  have he : X ^ (-(a + n)) = X ^ (-a) * X⁻¹ ^ n := by
    rw [show -(a + (n : ℝ)) = -a + -(n : ℝ) by ring,
      Real.rpow_add hX, Real.rpow_neg hX.le (n : ℝ), Real.rpow_natCast, inv_pow]
  rw [he, show 1 - (b.1 - a) = a - b.1 + 1 by ring]
  field_simp
  change Real.Gamma b.1 * poch (a - b.1 + 1) n * Real.rpow X (-a) * poch a n =
    Real.Gamma b.1 * poch (a - b.1 + 1) n * poch a n * Real.rpow X (-a)
  ring

/-- The negative-axis expansion for a positive first parameter. -/
theorem M_negative_expansion_positive (a : ℝ) (b : Pos)
    (ha : 0 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => X ^ (-a - (N : ℝ))) := by
  have h := (eulerLaplace_expansion a (b.1 - a) N ha (sub_pos.mpr hab))
    |>.const_mul_left (Real.Gamma b.1 / (Real.Gamma a * Real.Gamma (b.1 - a)))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [M_euler_integral a b ha hab (-X)]
    have he : (∫ t in (0 : ℝ)..1, Real.exp (-X * t) * betaWeight a (b.1 - a) t) =
        ∫ t in (0 : ℝ)..1, eulerLaplace a (b.1 - a) X t := by
      apply intervalIntegral.integral_congr
      intro t _
      change Real.exp (-X * t) * betaWeight a (b.1 - a) t =
        betaWeight a (b.1 - a) t * Real.exp (-(X * t))
      rw [neg_mul, mul_comm]
    rw [he, mul_sub, gammaPolynomial_normalized a b N X ha hab hX]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
