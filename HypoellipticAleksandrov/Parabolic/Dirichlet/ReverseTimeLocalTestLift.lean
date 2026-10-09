module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeTests

/-!
# Lifting local scalar tests to reverse time

This module regards an original-time scalar test on a subinterval as a reverse-time scalar
test whenever that subinterval lies in the reverse-time interval.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Regard a scalar test on a local time interval as a reverse-time scalar test. -/
def reverseTimeScalarTestOfLocal {τ₁ τ₂ T : ℝ}
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval T)
    (eta : OriginalTimeScalarTest τ₁ τ₂) : ReverseTimeScalarTest T where
  toFun := eta
  contDiff' := eta.contDiff
  hasCompactSupport' := eta.hasCompactSupport
  tsupport_subset' := eta.tsupport_subset.trans htime

@[simp] theorem reverseTimeScalarTestOfLocal_apply {τ₁ τ₂ T : ℝ}
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval T)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (τ : ℝ) :
    reverseTimeScalarTestOfLocal htime eta τ = eta τ :=
  rfl

@[simp] theorem reverseTimeScalarTestOfLocal_deriv {τ₁ τ₂ T : ℝ}
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval T)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (τ : ℝ) :
    (reverseTimeScalarTestOfLocal htime eta).deriv τ = eta.deriv τ :=
  rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
