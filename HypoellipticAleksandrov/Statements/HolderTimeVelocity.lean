module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.FinalA
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting

/-!
# Hölder continuity for time–velocity coefficients

Companion paper, Corollary 9.9. The Hörmander hypoellipticity theorem is supplied by the
`hormander` package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved
in this library, so the statement carries no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Companion paper, Corollary 9.9. -/
theorem kinetic_holder_timeVelocity
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
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_timeVelocity_proof
    d hd lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
