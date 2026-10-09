module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import Mathlib.Tactic

/-! # The permitted barrier interval and the occupation exponent arithmetic -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The source interval implies positivity and places the radial pair above the adjoint exponent. -/
theorem bellman_barrier_parameter_range (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) :
    0 < alpha ∧ alpha < 1 ∧
      bellmanAdjointExponent (Lam / lam)
        (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) < 2 + alpha := by
  have ht := bellmanAdjointExponent_two_le (Lam / lam)
    (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam)
  exact ⟨by linarith, ha1, by linarith⟩

/-- The occupation powers are literal arithmetic functions of the same chosen barrier degree. -/
theorem bellman_occupation_exponents (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    1 < 2 - alpha ∧ 2 - alpha < 2 ∧ 0 < 1 - alpha ∧
      1 - alpha = (2 - alpha) - 1 := by
  exact ⟨by linarith, by linarith, by linarith, by ring⟩

end HypoellipticAleksandrov.KineticAleksandrov
