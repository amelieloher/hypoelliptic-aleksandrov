module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsContinuation
import Mathlib.Tactic.Ring

/-!
# General negative-axis expansion

The proved contiguous relation extends Euler asymptotics to every first parameter above minus one.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/-- Monotonicity of algebraic asymptotic orders on the positive half-line. -/
theorem rpow_isBigO_of_le (r s : ℝ) (hrs : r ≤ s) :
    IsBigO atTop (fun X : ℝ => X ^ r) (fun X => X ^ s) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hX]) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hX hrs

/-- Continuation gives the expansion at every positive truncation order. -/
theorem M_negative_expansion_succ (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 (N + 1) X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have hab1 : a + 1 < (next b).1 := by change a + 1 < b.1 + 1; linarith only [hab]
  have hab2 : a + 1 < (next (next b)).1 := by
    change a + 1 < b.1 + 1 + 1
    linarith only [hab]
  have h1 := M_negative_expansion_positive (a + 1) (next b) ha1 hab1 N
  have h2 := M_negative_expansion_positive (a + 1) (next (next b)) ha1 hab2 (N + 1)
  have hb2 : (next (next b)).1 = b.1 + 2 := by dsimp [next]; ring
  rw [hb2] at h2
  have hX : IsBigO atTop (fun X : ℝ => X) (fun X => X ^ (1 : ℝ)) := by
    simpa only [Real.rpow_one] using (isBigO_refl (fun X : ℝ => X) atTop)
  have h2X := hX.mul_atTop_rpow_of_isBigO_rpow 1
    (-(a + 1) - ((N + 1 : ℕ) : ℝ)) (-a - ((N + 1 : ℕ) : ℝ)) h2 (by linarith)
  have h1' : IsBigO atTop
      (fun X => M (a + 1) (next b) (-X) - mExpansion (a + 1) (b.1 + 1) N X)
      (fun X => X ^ (-a - ((N + 1 : ℕ) : ℝ))) := by
    convert h1 using 1
    · rfl
    · ext X
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  have h := h1'.add (h2X.const_mul_left (-((a - b.1) / (b.1 * (b.1 + 1)))))
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hXp
    rw [M_contiguous a b (-X), mExpansion_contiguous a b hab N X hXp]
    simp only [Pi.mul_apply]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The complete algebraic expansion with its exact remainder order. -/
theorem M_negative_expansion (a : ℝ) (b : Pos)
    (ha : -1 < a) (hab : a < b.1) (N : ℕ) :
    IsBigO atTop (fun X => M a b (-X) - mExpansion a b.1 N X)
      (fun X => Real.rpow X (-a - (N : ℝ))) := by
  cases N with
  | succ N => exact M_negative_expansion_succ a b ha hab N
  | zero =>
    have h1 := (M_negative_expansion_succ a b ha hab 0).trans
      (rpow_isBigO_of_le (-a - ((0 + 1 : ℕ) : ℝ)) (-a) (by norm_num))
    have h0 : IsBigO atTop (mExpansion a b.1 1) (fun X : ℝ => X ^ (-a)) := by
      have h := (isBigO_refl (fun X : ℝ => X ^ (-a)) atTop)
        |>.const_mul_left (Real.Gamma b.1 / Real.Gamma (b.1 - a))
      convert h using 1
      ext X
      simp [mExpansion]
    have h := h1.add h0
    convert h using 1
    · ext X
      simp only [mExpansion, Finset.range_zero, Finset.sum_empty, mul_zero]
      ring
    · ext X
      simp only [Nat.cast_zero, sub_zero]
      rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
