module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Combining the structural constants of exit loss and Fourier decay -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA

/-- Enlarging the prefactor and decreasing the positive exponential rate combines
both estimates with one pair of structural constants. -/
theorem ballExit_combine_exponentials {A a B b x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    A * Real.exp (-a * x) + B * Real.exp (-b * y) ≤
      max A B * (Real.exp (-min a b * x) + Real.exp (-min a b * y)) := by
  have ha := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left a b)) hx)
  have hb := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right a b)) hy)
  have h1 := mul_le_mul (le_max_left A B) ha (Real.exp_pos _).le
    (hA.trans (le_max_left A B))
  have h2 := mul_le_mul (le_max_right A B) hb (Real.exp_pos _).le
    (hB.trans (le_max_right A B))
  exact (add_le_add h1 h2).trans_eq (mul_add _ _ _).symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
