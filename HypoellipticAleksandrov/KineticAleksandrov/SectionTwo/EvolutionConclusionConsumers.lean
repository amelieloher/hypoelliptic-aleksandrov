module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksContract
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityEvolution

/-! # Bridges from the shared evolution conclusion to existing consumers

The iteration and occupation premises are definitionally identical. Theorem A uses
only the whole-space, identity-drift specialization with the same shared witnesses.
Consumer files are read-only; the common definition is independent of these imports.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ProbabilityTheory MatrixOrder

/-- The iteration input is exactly the shared terminal evolution statement. -/
theorem iterationEvolutionStatement_of_conclusion (h : TerminalEvolutionConclusion) :
    Decay.IterationEvolutionStatement := h

/-- The occupation input is exactly the shared terminal evolution statement. -/
theorem occupationEvolutionStatement_of_conclusion (h : TerminalEvolutionConclusion) :
    Occupation.TerminalEvolutionStatement := h

/-- The premise of Theorem A follows by whole-space identity-drift specialization. -/
theorem taAssemblyEvolution_of_conclusion (h : TerminalEvolutionConclusion)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
          (zIndependentCoefficient B) σ y z = (zIndependentCoefficient B) σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
            MeasurableSet.univ K) ∧
        IsDomainMonotoneEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient B) (identityDrift d) K ∧
        HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K := by
  intro B hB
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, hcov, hmono, hpar⟩ :=
    h d hd lam Lam 1 1 hlam hlamLam one_pos le_rfl (wholeSpace d) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) (wholeSpace_admissible d)
      (zeroCurve_piecewiseC1 d) hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
  exact ⟨S, K, ⟨hc, hi, he, hcomp⟩, hcov, hmono, hpar⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
