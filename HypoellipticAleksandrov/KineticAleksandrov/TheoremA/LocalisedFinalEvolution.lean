module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusionConsumers
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier

/-! # Localized Theorem A assembly from the shared terminal evolution conclusion

The occupation, unit-frequency block, decay and slab bounds are discharged by their
proved results. This intermediate export retains the evolution conclusion explicitly.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory
open scoped ENNReal MatrixOrder

/-- The localized conclusion assembled from evolution and the two analytic hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hEv : SectionTwo.TerminalEvolutionConclusion)
    (hH : HormanderHypoellipticityStatement) :
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
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  have hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
  have hOcc := Occupation.parabolicOccupationFamily_holds
    (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam
  have hBlock := Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam
  have hDecay := Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter hBlock
  exact kinetic_aleksandrov_timeVelocity_localised_of_slabFourierBounds
    d hd lam Lam p hlam hLam hp hH
    (Green.slabFourierBounds_of_occupation_decay hd lam Lam hOcc hDecay)
    (SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam)

end HypoellipticAleksandrov.KineticAleksandrov
