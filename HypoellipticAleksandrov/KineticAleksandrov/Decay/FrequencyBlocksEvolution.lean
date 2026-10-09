module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksContract

/-! # Transfer of the evolution clauses to an arbitrary realizing kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The authorized evolution premise supplies all structural clauses on the given kernel. -/
theorem iteration_evolution_clauses (hEvol : IterationEvolutionStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) stationary)
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hreal : RealizesTerminalEvolution (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) S K) :
    IsDomainMonotoneEvolution (wholeSpace d) stationary
      (zIndependentCoefficient B) (identityDrift d) K ∧
    HasParabolicMarginalBundle (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) K ∧
    IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K := by
  obtain ⟨hBs, hBy, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  obtain ⟨P, K₀, hclass, hendpointP, hpos, hcontract, hcompP, hint,
    hsupp, hmass, hmeas, hfiber, hend, hcomp, hcov, hmono, hmargin⟩ :=
    hEvol d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl
      (wholeSpace d) stationary (zIndependentCoefficient B) (identityDrift d)
      (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) hBs hBy hBell
      (identityDrift_smooth d) (identityDrift_bounds d).1 (identityDrift_bounds d).2
  have hr₀ : RealizesTerminalEvolution (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) P K₀ :=
    ⟨hclass, hint, hend, hcomp⟩
  have hK := (terminalEvolution_unique (wholeSpace d) stationary (wholeSpace_admissible d)
    (zIndependentCoefficient B) (identityDrift d) S P K K₀ hreal hr₀).2
  subst K₀
  exact ⟨hmono, hmargin, hcov (fun _ _ _ _ => rfl)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
