module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Subcritical homogeneity exponent

Appendix C: choose the exponent before fixing the profile and coefficients.
-/

public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Every exponent below the kinetic threshold admits a positive source-decay exponent. -/
theorem exists_subcritical_alpha (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < alpha - 2 + 4 * (d : ℝ) / p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hratio : 1 < 4 * (d : ℝ) / p := (lt_div_iff₀ hp0).2 (by simpa using hpd)
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hratio0 : 0 < 4 * (d : ℝ) / p := div_pos (by positivity) hp0
  obtain ⟨alpha, ha, ha1⟩ := exists_between
    (show max (0 : ℝ) (2 - 4 * (d : ℝ) / p) < 1 from
      max_lt zero_lt_one (by linarith only [hratio]))
  refine ⟨alpha, lt_of_le_of_lt (le_max_left _ _) ha, ha1, ?_⟩
  have hlow := lt_of_le_of_lt (le_max_right (0 : ℝ) (2 - 4 * (d : ℝ) / p)) ha
  linarith only [hlow, hratio0]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
