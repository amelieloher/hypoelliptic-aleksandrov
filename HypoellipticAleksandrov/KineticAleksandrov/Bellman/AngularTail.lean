module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquation

/-! # Compatible angular representations, densities and tail estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A genuine homogeneous pair produces compatible angular measures, densities and finite
tails. -/
theorem exists_angular_densities_tail (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ (F H : Measure ℝ) (f h J : ℝ → ℝ),
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      (
      F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
      LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
      (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
      (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
      (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y)) ∧
      IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  obtain ⟨F, H, hrep, hang⟩ := exists_angular_adjoint R β hR hβ μ η hp
  obtain ⟨f, h, J, hd⟩ := angular_has_densities R β hR F H hang
  let : IsFiniteMeasureOnCompacts μ := hp.1.1
  let : IsFiniteMeasureOnCompacts F := hang.1
  exact ⟨F, H, f, h, J, hrep, hd,
    bellmanAngularDensity_tail β μ F hrep.1 f hd.1 hd.2.2.1 hd.2.2.2.1⟩

end HypoellipticAleksandrov.KineticAleksandrov
