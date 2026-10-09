module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksContract

/-! # Local supplied evolutions from the authorized evolution statement -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The sole authorized evolution input constructs a local tube realization
with the structural clauses on the same constructed kernel. -/
theorem exists_unitBlock_evolution (hEvol : IterationEvolutionStatement)
    {d : ℕ} (hd : 1 ≤ d) (lam Lam m Lb : ℝ)
    (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (hsetting : SourceSetting lam Lam m Lb D B b)
    (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) :
    ∃ (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ),
      RealizesTerminalEvolution Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        (zIndependentCoefficient B) b S K ∧
      IsDomainMonotoneEvolution Ω γ (zIndependentCoefficient B) b K ∧
      HasParabolicMarginalBundle Ω γ (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        (zIndependentCoefficient B) K ∧
      IsTranslationCovariantEvolution Ω γ
        (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K := by
  obtain ⟨hBs, hBy, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hsetting.1
  obtain ⟨S, K, hclass, -, -, -, -, hint,
    -, -, -, -, hend, hcomp, hcov, hmono, hmargin⟩ :=
    hEvol d hd lam Lam m Lb hsetting.1.1 hsetting.1.2.1 hsetting.2.2.1
      hsetting.2.2.2.1 Ω γ (zIndependentCoefficient B) b hΩ hγ hBs hBy hBell
      hsetting.2.1 hsetting.2.2.2.2.1.1 hsetting.2.2.2.2.1.2
  exact ⟨S, K, ⟨hclass, hint, hend, hcomp⟩, hmono, hmargin,
    hcov (fun _ _ _ _ => rfl)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
