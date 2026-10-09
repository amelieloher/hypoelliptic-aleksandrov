module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
import Mathlib.Tactic

/-!
# Exact differentiated scalar tail exports

The two source rays have a common leading coefficient at the matching diffusivity.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics

/-- The full source tail statement, including all three independently controlled jets. -/
theorem F_tail_jets (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (j : ℕ) (hj : j ≤ 2) :
    IsBigO atTop
      (Kummer.jet j (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 3 - (j : ℝ))) ∧
    IsBigO atBot
      (Kummer.jet j (fun s => Fminus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow |s| (3 * gamma.1)))
      (fun s => Real.rpow |s| (3 * gamma.1 - 3 - (j : ℝ))) := by
  have hnegative := Fminus_asymptotic gamma Lam hLam
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hnegative
  have hp := Fplus_tail_derivatives gamma Lam hLam
  have hn := Fminus_tail_derivatives gamma Lam hLam hmatch
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · simpa only [Kummer.jet, Function.iterate_zero_apply, Nat.cast_zero, sub_zero] using
      And.intro (Fplus_asymptotic gamma Lam hLam) hnegative
  · simpa only [Kummer.jet, Function.iterate_one, Nat.cast_one,
      show 3 * gamma.1 - 3 - 1 = 3 * gamma.1 - 4 by ring] using And.intro hp.1 hn.1
  · simpa only [Kummer.jet, Function.iterate_succ_apply, Function.iterate_zero_apply,
      Nat.cast_ofNat, show 3 * gamma.1 - 3 - 2 = 3 * gamma.1 - 5 by ring] using
      And.intro hp.2 hn.2

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
