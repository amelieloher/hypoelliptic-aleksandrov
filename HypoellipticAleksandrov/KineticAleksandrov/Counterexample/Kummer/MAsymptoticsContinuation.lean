module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsPositive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Continuation of the negative-axis expansion

A proved contiguous relation raises the first parameter above zero without changing the theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/-- The second contiguous coefficient after Gamma cancellation. -/
theorem expansionCoeff_contiguous_second (a : ℝ) (b : Pos) (hab : a < b.1) (n : ℕ) :
    -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) n =
      Real.Gamma b.1 / Real.Gamma (b.1 - a) *
        poch (a + 1) n * poch (a - b.1) n / (n.factorial : ℝ) := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hc := ne_of_gt (sub_pos.mpr hab)
  have hG := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
  rw [expansionCoeff, show b.1 + 2 = (b.1 + 1) + 1 by ring,
    Real.Gamma_add_one hb1, Real.Gamma_add_one hb,
    show (b.1 + 1 + 1) - (a + 1) = (b.1 - a) + 1 by ring,
    Real.Gamma_add_one hc, show a + 1 - (b.1 + 1 + 1) + 1 = a - b.1 by ring]
  field_simp
  ring

/-- The constant coefficient of the contiguous expansion. -/
theorem expansionCoeff_contiguous_zero (a : ℝ) (b : Pos) (hab : a < b.1) :
    expansionCoeff a b.1 0 = -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) 0 := by
  rw [expansionCoeff_contiguous_second a b hab]
  simp only [expansionCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]

/-- The higher coefficients of the contiguous expansion. -/
theorem expansionCoeff_contiguous_succ (a : ℝ) (b : Pos) (hab : a < b.1) (n : ℕ) :
    expansionCoeff a b.1 (n + 1) = expansionCoeff (a + 1) (b.1 + 1) n +
      -((a - b.1) / (b.1 * (b.1 + 1))) *
        expansionCoeff (a + 1) (b.1 + 2) (n + 1) := by
  rw [expansionCoeff_contiguous_second a b hab, expansionCoeff, expansionCoeff,
    Real.Gamma_add_one (ne_of_gt b.2),
    show b.1 + 1 - (a + 1) = b.1 - a by ring,
    show a + 1 - (b.1 + 1) + 1 = a - b.1 + 1 by ring,
    poch_succ_left a n, poch_succ (a - b.1 + 1) n,
    poch_succ (a + 1) n, poch_succ_left (a - b.1) n,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The exact matching of finite contiguous expansions at adjacent truncation orders. -/
theorem mExpansion_contiguous (a : ℝ) (b : Pos) (hab : a < b.1) (N : ℕ)
    (X : ℝ) (hX : 0 < X) :
    mExpansion a b.1 (N + 1) X = mExpansion (a + 1) (b.1 + 1) N X +
      (-((a - b.1) / (b.1 * (b.1 + 1))) * X) *
        mExpansion (a + 1) (b.1 + 2) (N + 1) X := by
  rw [mExpansion_eq_sum a b.1 (N + 1) X hX,
    mExpansion_eq_sum (a + 1) (b.1 + 1) N X hX,
    mExpansion_eq_sum (a + 1) (b.1 + 2) (N + 1) X hX]
  let k : ℝ := -((a - b.1) / (b.1 * (b.1 + 1)))
  have hx (n : ℕ) : X * Real.rpow X (-(a + 1 + n)) = Real.rpow X (-(a + n)) := by
    change X * X ^ (-(a + 1 + (n : ℝ))) = X ^ (-(a + n))
    calc
      _ = X ^ (1 : ℝ) * X ^ (-(a + 1 + (n : ℝ))) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + -(a + 1 + n)) := (Real.rpow_add hX _ _).symm
      _ = _ := by congr 1; ring
  have hm : (k * X) *
      (∑ n ∈ Finset.range (N + 1), expansionCoeff (a + 1) (b.1 + 2) n *
        Real.rpow X (-(a + 1 + n))) =
      ∑ n ∈ Finset.range (N + 1), k * expansionCoeff (a + 1) (b.1 + 2) n *
        Real.rpow X (-(a + n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    calc
      _ = (k * expansionCoeff (a + 1) (b.1 + 2) n) *
          (X * Real.rpow X (-(a + 1 + n))) := by ring
      _ = _ := by rw [hx]
  change _ = _ + (k * X) * _
  rw [hm]
  have ht (n : ℕ) : expansionCoeff a b.1 (n + 1) *
      Real.rpow X (-(a + (n + 1 : ℕ))) =
      expansionCoeff (a + 1) (b.1 + 1) n * Real.rpow X (-(a + 1 + n)) +
      k * expansionCoeff (a + 1) (b.1 + 2) (n + 1) *
        Real.rpow X (-(a + (n + 1 : ℕ))) := by
    rw [expansionCoeff_contiguous_succ a b hab n]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show a + ((n : ℝ) + 1) = a + 1 + n by ring]
    dsimp [k]
    ring
  have hs := Finset.sum_congr (s₁ := Finset.range N) rfl (fun n _ => ht n)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [expansionCoeff_contiguous_zero a b hab]
  change _ + k * _ * _ = _ + (_ + k * _ * _)
  linarith only [hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
