module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Literal angular adjoint equation on the real line -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- The source angular equation with the literal measure comparison bounds.
No density, regularity of a density, or moment bound is included in this predicate. -/
def IsBellmanAngularAdjointPair (lam Lam β : ℝ) (F H : Measure ℝ) : Prop :=
  IsFiniteMeasureOnCompacts F ∧ Measure.InnerRegular F ∧
    IsFiniteMeasureOnCompacts H ∧ Measure.InnerRegular H ∧ ENNReal.ofReal lam • F ≤ H ∧
    H ≤ ENNReal.ofReal Lam • F ∧
    ∀ (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, deriv (deriv φ) y ∂H) - (1 / 3 : ℝ) * (∫ y, y ^ 2 * deriv φ y ∂F) +
        ((β - 2) / 3) * (∫ y, y * φ y ∂F) = 0

end HypoellipticAleksandrov.KineticAleksandrov
