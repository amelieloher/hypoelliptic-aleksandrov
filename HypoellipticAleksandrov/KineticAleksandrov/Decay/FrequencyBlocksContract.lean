module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Fourier

/-! # Exact authorized conditional inputs for Section 3 iteration

The evolution input is the terminal evolution statement with its structural predicates.
The unit-block input is the unit-block estimate of the companion paper, Proposition 3.9,
including all binder data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ProbabilityTheory MatrixOrder

/-- The terminal evolution statement (companion paper, Proposition 2.1). -/
def IterationEvolutionStatement : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b),
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
            (hE : MeasurableSet E),
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
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z'),
          IsTranslationCovariantEvolution Ω γ
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
        IsDomainMonotoneEvolution Ω γ B b K ∧
        HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K

/-- The exact planned unit-frequency block statement, used conditionally. -/
def UnitBlockStatement (d : ℕ) (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) : Prop :=
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d),
        SourceSetting lam Lam m Lb D B b →
      ∀ (hD : MeasurableSet D) (S : TerminalOperatorFamily D stationary)
        (K : MovingFiberKernel D stationary),
        RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b S K →
        IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b K →
        HasParabolicMarginalBundle D stationary hD (zIndependentCoefficient B) K →
        IsTranslationCovariantEvolution D stationary hD K →
      ∀ (ξ : PDE.Vec d), PDE.vecNormSq ξ = 1 →
      ∀ (σ : ℝ) (v : PDE.Vec d) (hv : v ∈ movingDomain D stationary σ)
        (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec d)),
        IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ

/-- The unit-frequency block statement in case W (`D = ℝ^d`), Proposition 3.9.
It is `UnitBlockStatement` restricted to the whole-space domain. -/
def UnitBlockStatementW (d : ℕ) (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) : Prop :=
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d),
        SourceSetting lam Lam m Lb D B b → D = univ →
      ∀ (hD : MeasurableSet D) (S : TerminalOperatorFamily D stationary)
        (K : MovingFiberKernel D stationary),
        RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b S K →
        IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b K →
        HasParabolicMarginalBundle D stationary hD (zIndependentCoefficient B) K →
        IsTranslationCovariantEvolution D stationary hD K →
      ∀ (ξ : PDE.Vec d), PDE.vecNormSq ξ = 1 →
      ∀ (σ : ℝ) (v : PDE.Vec d) (hv : v ∈ movingDomain D stationary σ)
        (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec d)),
        IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ

/-- The full unit-block statement implies its case-W restriction. -/
theorem unitBlockStatementW_of_unitBlockStatement {d : ℕ} {hd : 1 ≤ d}
    {lam Lam m Lb : ℝ} {hlam : 0 < lam} {hlamLam : lam ≤ Lam} {hm : 0 < m} {hmLb : m ≤ Lb}
    (h : UnitBlockStatement d hd lam Lam m Lb hlam hlamLam hm hmLb) :
    UnitBlockStatementW d hd lam Lam m Lb hlam hlamLam hm hmLb := by
  obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := h
  exact ⟨L, δ, hL, hδ, hδ1, fun D B b hs _ => hunit D B b hs⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
