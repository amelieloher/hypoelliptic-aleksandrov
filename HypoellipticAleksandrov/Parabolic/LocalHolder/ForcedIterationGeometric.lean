module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # The numerical forced dyadic iteration

A slower geometric envelope absorbs the summable quadratic forcing. This lemma is
pure real arithmetic, independent of any PDE or assumed regularity conclusion.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder

/-- A geometric envelope absorbs a recurrence with quadratic dyadic forcing. -/
theorem forced_recurrence_le_geometric
    {θ q E K : ℝ} (hθ : 0 ≤ θ) (hq : (1 / 4 : ℝ) ≤ q)
    (hE : 0 ≤ E) (hgap : E ≤ (q - θ) * K)
    (f : ℕ → ℝ) (hf0 : f 0 ≤ K)
    (hf : ∀ n, f (n + 1) ≤ θ * f n + E * (1 / 4 : ℝ) ^ n) :
    ∀ n, f n ≤ K * q ^ n := by
  intro n
  induction n with
  | zero => simpa only [pow_zero, mul_one] using hf0
  | succ n ih =>
    have hpow : (1 / 4 : ℝ) ^ n ≤ q ^ n := pow_le_pow_left₀ (by norm_num) hq n
    have hforce : E * (1 / 4 : ℝ) ^ n ≤ ((q - θ) * K) * q ^ n :=
      (mul_le_mul_of_nonneg_left hpow hE).trans
        (mul_le_mul_of_nonneg_right hgap (pow_nonneg (by linarith only [hq]) n))
    calc f (n + 1) ≤ θ * f n + E * (1 / 4 : ℝ) ^ n := hf n
      _ ≤ θ * (K * q ^ n) + ((q - θ) * K) * q ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hθ) hforce
      _ = K * q ^ (n + 1) := by rw [pow_succ]; ring

end HypoellipticAleksandrov.Parabolic.LocalHolder
