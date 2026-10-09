module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.Parabolic.KineticClassical
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Exact conditional boundary for the joint local time–velocity regularity theorem

This is the planned p:local-A type, including both spatial conclusions. It is an
unproved input boundary, not an internally established local regularity theorem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Parabolic LocalA
open scoped MatrixOrder

/-- Exact planned type of `local_timeVelocity_regularities_of_externals`. -/
def LocalTimeVelocityRegularityStatement : Prop :=
    ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    ∃ (C_m : ℕ → ℝ) (C α : ℝ), (∀ m, 0 ≤ C_m m) ∧ 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u : KineticPoint d → ℝ),
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
        (∀ P ∈ backwardCylinder P₀ R,
          ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
        (∀ (m : ℕ), 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
          R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
            C_m m * Holder.oscillationOn u (backwardCylinder P₀ R)) ∧
        (∀ P ∈ backwardCylinder P₀ (R / 2),
          ∀ Q ∈ backwardCylinder P₀ (R / 2),
            |u P - u Q| ≤ C * Holder.oscillationOn u (backwardCylinder P₀ R) *
              (kineticIncrement P₀ P Q / R) ^ α)

end HypoellipticAleksandrov.KineticAleksandrov
