module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure

/-!
# Kinetic Aleksandrov estimate for time–velocity coefficients

Companion paper, Theorem 1.1: the Aleksandrov estimate for kinetic operators with
coefficients depending on time and velocity. The Hörmander hypoellipticity theorem is
supplied by the `hormander` package and classical Dirichlet solvability (Lieberman,
Theorem 5.14) is proved in this library, so the statement carries no extra hypotheses.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace KineticAleksandrov

/-- Companion paper, Theorem 1.1, with the uniform constant quantified before the data. -/
theorem kinetic_aleksandrov_timeVelocity
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity_proof
    d hd lam Lam p hlam hLam hp

end KineticAleksandrov

end HypoellipticAleksandrov
