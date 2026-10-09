module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Tactic

/-! # The integrated angular identity for the actual density and flux representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Two integrations of the actual density and flux give the source angular identity. -/
theorem angular_integrated (R β : ℝ) (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y)) :
    ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y * bellmanAngularFirstMoment f y +
      ((β - 3) / 3) * bellmanAngularSecondMoment f y := by
  exact bellmanAngularDensity_integrated β f h J hd.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2

end HypoellipticAleksandrov.KineticAleksandrov
