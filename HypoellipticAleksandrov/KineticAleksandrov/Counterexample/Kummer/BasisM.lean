module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Basis
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
import Mathlib.Tactic

/-!
# The second real solution on the positive axis

The power transformation of M supplies a second solution. Its positive shifted shape
makes this second solution nonzero on the whole positive axis.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Positive first parameters give strictly positive series coefficients. -/
theorem coeff_pos (a b : Pos) (n : ℕ) : 0 < coeff a.1 b n := by
  exact div_pos (poch_pos a n)
    (mul_pos (poch_pos b n) (by exact_mod_cast Nat.factorial_pos n))

/-- For positive first parameters, M is at least its constant term on the positive ray. -/
theorem one_le_M (a b : Pos) (z : ℝ) (hz : 0 ≤ z) : 1 ≤ M a.1 b z := by
  have h := (hasSum_M a.1 b z).summable.sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => mul_nonneg (coeff_pos a b n).le (pow_nonneg hz n))
  simpa only [Finset.sum_singleton, coeff_zero, pow_zero, mul_one, M] using h

/-- The second solution, with an actual real positive-axis power. -/
def secondM (a : ℝ) (z : ℝ) : ℝ :=
  z ^ (1 / 3 : ℝ) * M (a + 1 / 3) b43 z

/-- The second positive-axis solution never vanishes for the source parameter range. -/
theorem secondM_pos (a : NegThird) (z : ℝ) (hz : 0 < z) : 0 < secondM a.1 z := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  exact mul_pos (Real.rpow_pos_of_pos hz _) (lt_of_lt_of_le zero_lt_one (one_le_M c b43 z hz.le))

/-- Smoothness of the second solution away from the singular point. -/
theorem contDiffOn_secondM (a : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (secondM a) (Ioi 0) := by
  have hm : ContDiffOn ℝ (⊤ : ℕ∞) (M (a + 1 / 3) b43) (Ioi 0) :=
    ((analyticOnNhd_M (a + 1 / 3) b43).contDiffOn uniqueDiffOn_univ).mono (subset_univ _)
  exact (contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)).mul hm

/-- The second M solution solves the same Kummer equation as the first. -/
theorem secondM_ode (a z : ℝ) (hz : 0 < z) :
    z * deriv (deriv (secondM a)) z +
      (2 / 3 - z) * deriv (secondM a) z - a * secondM a z = 0 := by
  have hm := analyticOnNhd_M (a + 1 / 3) b43
  have hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt (M (a + 1 / 3) b43)
      (deriv (M (a + 1 / 3) b43) w) w := by
    intro w _
    exact (hm w (mem_univ _)).differentiableAt.hasDerivAt
  have hc : ContDiffAt ℝ 2 (M (a + 1 / 3) b43) z := (hm z (mem_univ _)).contDiffAt
  have hd := (hc.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have ho := M_ode (a + 1 / 3) b43 z
  have h := power_mul_kummer_ode (M (a + 1 / 3) b43) (a + 1 / 3) (1 / 3) z hz hf
    hd.hasDerivAt (by norm_num [b43] at ho ⊢; exact ho)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    show a + 1 / 3 - 1 / 3 = a by ring] at h
  change z * deriv (deriv (fun w => w ^ (1 / 3 : ℝ) * M (a + 1 / 3) b43 w)) z +
    (2 / 3 - z) * deriv (fun w => w ^ (1 / 3 : ℝ) * M (a + 1 / 3) b43 w) z -
    a * (z ^ (1 / 3 : ℝ) * M (a + 1 / 3) b43 z) = 0
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
