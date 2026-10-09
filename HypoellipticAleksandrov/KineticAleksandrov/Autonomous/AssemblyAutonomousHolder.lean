module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousHolder

/-! # Exact autonomous headline surface relative to the remaining frontier

Pure composition of results. The four source steps and three
classical inputs remain explicit; this is a conditional theorem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder
open scoped ENNReal

/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_holder_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
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
  exact kinetic_holder_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
