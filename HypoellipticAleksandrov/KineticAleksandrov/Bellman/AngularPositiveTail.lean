module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegrated
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailLimitCalculus

/-! # The positive-tail limit for actual angular densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Actual angular densities of degree at least three satisfy the source positive-tail limit. -/
theorem angular_positive_tail_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 L) ∧
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) ∧
      J 0 = ((β - 2) / 3) * L ∧ ∀ y : ℝ, 0 < y → h 0 ≤ h y := by
  have hh := bellmanAngularDensity_nonneg hd.2.2.2.2.1 hd.2.2.2.1
    (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))
  exact bellmanAngularPositiveTail_limit R β hR hβ f h J hd.2.2.1 hd.2.2.2.1 hh
    (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)) he htail

end HypoellipticAleksandrov.KineticAleksandrov
