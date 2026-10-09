module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting

/-!
# Hölder continuity for autonomous coefficients (d = 1)

Companion paper, Corollary 9.10. The Hörmander hypoellipticity theorem is supplied by the
`hormander` package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved
in this library, so the statement carries no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Companion paper, Corollary 9.10. -/
theorem kinetic_holder_autonomous
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_autonomous_proof
    lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
