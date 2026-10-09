module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.TimeVelocityCorollary
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Assembly

/-! # Time–velocity Hölder assembly from the smooth joint local statement -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder LocalA
open scoped MatrixOrder

/-- The exact relative Hölder conclusion conditional on the smooth joint local statement. -/
theorem kinetic_holder_timeVelocity_relative_of_smooth
    (h : SmoothLocalRegularityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact kinetic_holder_timeVelocity_relative_of_local
    (localTimeVelocityRegularity_of_smooth h) hH hLE d hd lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
