module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityFromBound
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceBound

/-!
# The unit-time occupation duality

The whole-space source estimate is consumed at its complete form. The smooth-test
density theorem proves absolute continuity internally; one density works at every exponent.
The only analytic inputs are the explicit hypotheses of Hörmander's hypoellipticity theorem
and classical Dirichlet solvability (Lieberman, Theorem 5.14).
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal

variable {d : ℕ}

/-- Unit-time occupation density with uniform constants and the full exponent range. -/
theorem occupation_duality
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal := by
  exact occupation_duality_of_whole_space_bound hH hd lam Lam hlam hLam
    (occupation_whole_space_bound hH hd lam Lam hlam hLam)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
