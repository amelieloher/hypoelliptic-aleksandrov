module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-!
# The exact evolution premise and transfer to an arbitrary realization

The premise is the terminal evolution statement (companion paper, Proposition 2.1),
spelled out with the clause predicates of `SectionTwo`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder ProbabilityTheory

/-- The entire terminal evolution statement, retaining its shared witnesses and clauses. -/
def TerminalEvolutionStatement : Prop :=
  ∀
    (n : ℕ) (_hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (_hlam : 0 < lam) (_hlamLam : lam ≤ Lam)
    (_hm : 0 < m) (_hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (_hγ : IsContinuousPiecewiseC1 γ)
    (_hB_smooth : IsSmoothFullKineticCoefficient B)
    (_hB_symm : IsSymmetricFullKineticCoefficient B)
    (_hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (_hb_smooth : IsSmoothDrift b)
    (_hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (_hb_coercive : HasUnitDirectionDriftCoercivity m b),
    ∃ P : TerminalOperatorFamily Ω γ,
      ∃ K : MovingFiberKernel Ω γ,
        (∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
          IsSmoothCompactTerminalDatum Ω γ τ F →
            ∃ u : KineticPoint n → ℝ,
              IsClassicalTerminalSolution Ω γ B b τ F u ∧
              (∀ (σ : ℝ) (hστ : σ ≤ τ)
                  (p : EvolutionState Ω γ σ),
                u ⟨σ, p.1.1, p.1.2⟩ =
                  P σ τ hστ (terminalStateDatum F) p) ∧
              (∀ v : KineticPoint n → ℝ,
                IsClassicalTerminalSolution Ω γ B b τ F v →
                  EqOn v u (evolutionPastClosedCylinder Ω γ τ))) ∧
        (∀ (σ : ℝ),
          P σ σ le_rfl =
            (LinearMap.id :
              BoundedBorel (EvolutionState Ω γ σ) →ₗ[ℝ]
                BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          0 ≤ f → 0 ≤ P σ τ hστ f) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
          P σ τ hστ (1 : BoundedBorel (EvolutionState Ω γ τ)) ≤
            (1 : BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
          P σ τ (hσr.trans hrτ) =
            (P σ r hσr).comp (P r τ hrτ)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          P σ τ hστ f p =
            ∫ q, f q ∂(K.fiberKernel
              (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
              σ τ hστ p)) ∧
        (∀ q : EvolutionQuery Ω γ,
          (K.master q).restrict (evolutionStateSet Ω γ q.1.2.1) =
            K.master q) ∧
        (∀ q : EvolutionQuery Ω γ, K.master q Set.univ ≤ 1) ∧
        (∀ (E : Set (EvolutionAmbientState n))
            (_hE : MeasurableSet E),
          Measurable (fun q : EvolutionQuery Ω γ => K.master q E)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ),
          K.fiberKernel
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
            σ τ hστ p Set.univ ≤ 1) ∧
        MovingFiberKernel.HasEndpoint K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        MovingFiberKernel.HasComposition K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        (∀ hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z',
          let _ := hBz
          IsTranslationCovariantEvolution Ω γ
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
        IsDomainMonotoneEvolution Ω γ B b K ∧
        HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K

/-- Transfer the source clauses by uniqueness, rather than assuming them for the given kernel. -/
theorem evolution_clauses_of_realization
    (hEvol : TerminalEvolutionStatement)
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
    (hBell : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
    (hbl : HasEuclideanLipschitzDrift L_b b) (hbc : HasUnitDirectionDriftCoercivity m b)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K) :
    (∀ hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z',
      let _ := hBz
      IsTranslationCovariantEvolution Ω γ
        (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
    IsDomainMonotoneEvolution Ω γ B b K ∧
    HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K := by
  obtain ⟨S₀, K₀, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, hcov, hdom, hpar⟩ :=
    hEvol n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hBs hBsym hBell
      hbs hbl hbc
  have hr₀ : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S₀ K₀ :=
    ⟨hc, hi, he, hcomp⟩
  have hunique := terminalEvolution_unique Ω γ hΩ B b S S₀ K K₀ hreal hr₀
  rw [hunique.2]
  exact ⟨hcov, hdom, hpar⟩

/-- The full evolution premise supplies the marginal bundle for every whole-space realization. -/
theorem wholeSpace_marginalBundle_of_evolution
    (hEvol : TerminalEvolutionStatement) {d : ℕ} (hd : 0 < d)
    {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K) :
    HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K := by
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  exact (evolution_clauses_of_realization hEvol d hd lam Lam 1 1 hB.1 hB.2.1
    one_pos le_rfl (wholeSpace d) (fun _ => 0) (zIndependentCoefficient B)
    (identityDrift d) (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d)
    hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2 S K hreal).2.2

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
