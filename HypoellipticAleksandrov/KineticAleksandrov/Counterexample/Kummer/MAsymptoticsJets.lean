module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsGeneral
import Mathlib.Tactic.Ring

/-!
# First and second derivative remainders

The derivative estimates are obtained from proved parameter-shift identities and finite sums.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/-- The first derivative of the literal negative-axis expansion error. -/
theorem hasDerivAt_M_negative_remainder (a : ℝ) (b : Pos) (N : ℕ)
    (X : ℝ) (hX : 0 < X) :
    HasDerivAt (fun Y => M a b (-Y) - mExpansion a b.1 N Y)
      (-(a / b.1) *
        (M (a + 1) (next b) (-X) - mExpansion (a + 1) (next b).1 N X)) X := by
  have hM := (hasDerivAt_M a b (-X)).comp X (hasDerivAt_id X).neg
  have hE := hasDerivAt_mExpansion a b N X hX
  convert hM.sub hE using 1
  · rfl
  · rw [show (next b).1 = b.1 + 1 from rfl]
    ring

/-- The second derivative of the literal negative-axis expansion error. -/
theorem deriv2_M_negative_remainder (a : ℝ) (b : Pos) (N : ℕ)
    (X : ℝ) (hX : 0 < X) :
    deriv (deriv (fun Y => M a b (-Y) - mExpansion a b.1 N Y)) X =
      (-(a / b.1) * -((a + 1) / (next b).1)) *
        (M (a + 1 + 1) (next (next b)) (-X) -
          mExpansion (a + 1 + 1) (next (next b)).1 N X) := by
  have hd := (hasDerivAt_M_negative_remainder (a + 1) (next b) N X hX)
    |>.const_mul (-(a / b.1))
  have he : deriv (fun Y => M a b (-Y) - mExpansion a b.1 N Y) =ᶠ[nhds X]
      (fun Y => -(a / b.1) *
        (M (a + 1) (next b) (-Y) - mExpansion (a + 1) (next b).1 N Y)) := by
    filter_upwards [eventually_gt_nhds hX] with Y hY
    exact (hasDerivAt_M_negative_remainder a b N Y hY).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  ring

/-- The expansion error and its first two ordinary derivative jets have exact algebraic orders. -/
theorem M_negative_expansion_jet (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N j : ℕ) (hj : j ≤ 2) :
    IsBigO atTop
      (jet j (fun X => M a b (-X) - mExpansion a b.1 N X))
      (fun X => Real.rpow X (-a - (N : ℝ) - (j : ℝ))) := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have hab1 : a + 1 < (next b).1 := by
    change a + 1 < b.1 + 1
    linarith only [hab]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst j
    simpa only [jet, Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero] using
      M_negative_expansion a b ha hab N
  · subst j
    have h := (M_negative_expansion_positive (a + 1) (next b) ha1 hab1 N)
      |>.const_mul_left (-(a / b.1))
    apply h.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      simpa only [jet, Function.iterate_one, id_eq] using
        (hasDerivAt_M_negative_remainder a b N X hX).deriv.symm
    · exact Filter.Eventually.of_forall (fun X => by
        simp only [Nat.cast_one]
        change Real.rpow X (-(a + 1) - (N : ℝ)) =
          Real.rpow X (-a - (N : ℝ) - (1 : ℝ))
        congr 1
        ring)
  · subst j
    have ha2 : 0 < a + 1 + 1 := by linarith only [ha1]
    have hab2 : a + 1 + 1 < (next (next b)).1 := by
      change a + 1 + 1 < b.1 + 1 + 1
      linarith only [hab]
    have h := (M_negative_expansion_positive (a + 1 + 1) (next (next b)) ha2 hab2 N)
      |>.const_mul_left (-(a / b.1) * -((a + 1) / (next b).1))
    apply h.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      simpa only [jet, Function.iterate_succ_apply, Function.iterate_zero, id_eq] using
        (deriv2_M_negative_remainder a b N X hX).symm
    · exact Filter.Eventually.of_forall (fun X => by
        simp only [Nat.cast_ofNat]
        change Real.rpow X (-(a + 1 + 1) - (N : ℝ)) =
          Real.rpow X (-a - (N : ℝ) - (2 : ℝ))
        congr 1
        ring)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
