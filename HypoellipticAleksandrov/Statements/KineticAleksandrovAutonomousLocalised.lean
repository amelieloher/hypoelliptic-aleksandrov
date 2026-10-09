module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Localised kinetic Aleksandrov estimate for autonomous coefficients

Companion paper, Corollary 1.3 (localised form of Theorem 1.2). The Hörmander
hypoellipticity theorem is supplied by the `hormander` package and classical Dirichlet
solvability (Lieberman, Theorem 5.14) is proved in this library, so the statement carries
no extra hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- Localized autonomous scalar Aleksandrov estimate (companion paper, Corollary 1.3). -/
theorem kinetic_aleksandrov_autonomous_localised
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_localised_proof
    lam Lam p hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov
