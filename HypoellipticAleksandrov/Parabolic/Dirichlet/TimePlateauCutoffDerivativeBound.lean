module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePlateauCutoff

/-!
# Derivative-bound reverse-time plateau cutoffs

This module augments the reverse-time scalar plateau cutoff with a global bound
for its ordinary derivative.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A reverse-time scalar plateau cutoff together with a nonnegative global bound on its
ordinary derivative. -/
theorem exists_reverseTimeScalarTest_plateau_with_deriv_bound
    (T a b c d : ℝ)
    (ha0 : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hdT : d ≤ T) :
    ∃ (ζ : ReverseTimeScalarTest T) (Kζ : ℝ),
      0 ≤ Kζ ∧
      (∀ τ : ℝ, 0 ≤ ζ τ) ∧
      (∀ τ : ℝ, ζ τ ≤ 1) ∧
      (∀ τ ∈ Set.Icc b c, ζ τ = 1) ∧
      tsupport (ζ : ℝ → ℝ) ⊆ Set.Ioo a d ∧
      ∀ τ : ℝ, |ζ.deriv τ| ≤ Kζ := by
  obtain ⟨ζ, hζnonneg, hζle_one, hζplateau, hζsupport⟩ :=
    exists_reverseTimeScalarTest_plateau T a b c d ha0 hab hbc hcd hdT
  obtain ⟨C, hC⟩ := ζ.exists_norm_deriv_le
  refine ⟨ζ, max C 0, le_max_right C 0, hζnonneg, hζle_one, hζplateau, hζsupport, ?_⟩
  intro τ
  simpa only [Real.norm_eq_abs] using (hC τ).trans (le_max_left C 0)

end HypoellipticAleksandrov.Parabolic.Dirichlet
