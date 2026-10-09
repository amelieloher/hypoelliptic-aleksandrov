module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Contiguous relations for the literal Kummer series

These identities raise the first parameter while preserving positive Euler endpoint parameters.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Compatibility of the two rising-factorial recurrences. -/
theorem poch_shift (a : ℝ) (n : ℕ) :
    a * poch (a + 1) n = (a + n) * poch a n := by
  rw [← poch_succ_left, poch_succ, mul_comm]

/-- The coefficient identity underlying the positive-parameter continuation. -/
theorem coeff_contiguous_succ (a : ℝ) (b : Pos) (n : ℕ) :
    coeff a b (n + 1) = coeff (a + 1) (next b) (n + 1) +
      ((a - b.1) / (b.1 * (b.1 + 1))) * coeff (a + 1) (next (next b)) n := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hp1 := ne_of_gt (poch_pos (next b) n)
  have hp2 := ne_of_gt (poch_pos (next (next b)) n)
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs := poch_shift (b.1 + 1) n
  change (b.1 + 1) * poch (next (next b)).1 n =
    (b.1 + 1 + n) * poch (next b).1 n at hs
  simp only [coeff, poch_succ_left a n, poch_succ (a + 1) n,
    poch_succ_left b.1 n, poch_succ_left (next b).1 n,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  change a * poch (a + 1) n / (b.1 * poch (next b).1 n * ((n + 1) * n.factorial)) =
    poch (a + 1) n * (a + 1 + n) /
      ((b.1 + 1) * poch (next (next b)).1 n * ((n + 1) * n.factorial)) +
      (a - b.1) / (b.1 * (b.1 + 1)) *
        (poch (a + 1) n / (poch (next (next b)).1 n * n.factorial))
  field_simp
  have hsm := congrArg (fun x : ℝ => a * poch (a + 1) n * x) hs
  nlinarith only [hsm]

/-- A contiguous relation expressing all admissible parameters through positive Euler ones. -/
theorem M_contiguous (a : ℝ) (b : Pos) (z : ℝ) :
    M a b z = M (a + 1) (next b) z +
      ((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z := by
  have hs := (hasSum_M (a + 1) (next (next b)) z).mul_left
    ((a - b.1) * z / (b.1 * (b.1 + 1)))
  have he (n : ℕ) :
      ((a - b.1) * z / (b.1 * (b.1 + 1))) *
        (coeff (a + 1) (next (next b)) n * z ^ n) =
      ((a - b.1) / (b.1 * (b.1 + 1))) *
        coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
    rw [pow_succ]
    ring
  simp only [he] at hs
  let f : ℕ → ℝ := fun n => (coeff a b n - coeff (a + 1) (next b) n) * z ^ n
  have hf (n : ℕ) : f (n + 1) =
      ((a - b.1) / (b.1 * (b.1 + 1))) *
        coeff (a + 1) (next (next b)) n * z ^ (n + 1) := by
    dsimp [f]
    rw [coeff_contiguous_succ]
    ring
  have hsum : HasSum f
      (((a - b.1) * z / (b.1 * (b.1 + 1))) * M (a + 1) (next (next b)) z) := by
    have h0 : f 0 = 0 := by simp [f]
    simpa only [h0, zero_add] using (hs.congr_fun (fun n => hf n)).zero_add (f := f)
  have hdiff := (hasSum_M a b z).sub (hasSum_M (a + 1) (next b) z)
  have hdiff' : HasSum f (M a b z - M (a + 1) (next b) z) := by
    convert hdiff using 1
    ext n
    dsimp [f]
    ring
  have h := hdiff'.unique hsum
  linarith only [h]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
