module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.LocalStatement

/-! # Smooth joint local regularity input

This is the conditional input authorized by IMPL-LOCALA-10. Its binders match the
joint local statement, replacing Borel by smooth coefficients and omitting
`hLS`. Both spatial conclusions are retained; constants precede all coefficient,
cylinder and solution data. No smooth estimate is asserted here.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic
open scoped MatrixOrder

/-- Joint smooth-coefficient spatial and Hölder estimate consumed by the Borel limit. -/
def SmoothLocalRegularityStatement : Prop :=
    ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    ∃ (C_m : ℕ → ℝ) (C α : ℝ), (∀ m, 0 ≤ C_m m) ∧ 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField d),
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
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

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
