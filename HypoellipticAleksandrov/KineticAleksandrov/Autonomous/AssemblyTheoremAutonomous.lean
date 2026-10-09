module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TheoremAutonomous

/-! # Exact autonomous headline surface relative to the remaining frontier

Pure composition of results. The four source steps and three
classical inputs remain explicit; this is a conditional theorem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous TheoremA
open scoped ENNReal

/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_aleksandrov_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
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
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam p hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov
