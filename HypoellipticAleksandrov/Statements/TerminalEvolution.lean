module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Terminal evolution

Companion paper, Proposition 2.1: existence of the terminal evolution for the operators of
Section 2. The Hörmander hypoellipticity theorem is supplied by the `hormander` package and
classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved in this library, so the
statement carries no extra hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder ProbabilityTheory

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The shared-witness terminal-evolution statement. -/
theorem exists_terminalEvolution
    (n : ℕ) (hn : 1 ≤ n)
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
    (hb_coercive : HasUnitDirectionDriftCoercivity m b) :
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
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n),
              B σ y z = B σ y z'),
          ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n)
              (p : EvolutionState Ω γ σ),
            Measure.map (evolutionStateShift Ω γ τ h)
                (K.fiberKernel
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ τ hστ p) =
              K.fiberKernel
                (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                σ τ hστ (evolutionStateShift Ω γ σ h p)) ∧
        (∀ (Ω' : Set (PDE.Vec n)) (γ' : ℝ → PDE.Vec n)
            (hΩ' : IsAdmissibleEvolutionDomain Ω')
            (hγ' : IsContinuousPiecewiseC1 γ')
            (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆
              movingDomain Ω γ σ)
            (P' : TerminalOperatorFamily Ω' γ')
            (K' : MovingFiberKernel Ω' γ'),
          ((∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
              IsSmoothCompactTerminalDatum Ω' γ' τ F →
                ∃ u : KineticPoint n → ℝ,
                  IsClassicalTerminalSolution Ω' γ' B b τ F u ∧
                  (∀ (σ : ℝ) (hστ : σ ≤ τ)
                      (p : EvolutionState Ω' γ' σ),
                    u ⟨σ, p.1.1, p.1.2⟩ =
                      P' σ τ hστ (terminalStateDatum F) p) ∧
                  (∀ v : KineticPoint n → ℝ,
                    IsClassicalTerminalSolution Ω' γ' B b τ F v →
                      EqOn v u (evolutionPastClosedCylinder Ω' γ' τ)))) ∧
           (∀ (σ : ℝ),
             P' σ σ le_rfl =
               (LinearMap.id :
                 BoundedBorel (EvolutionState Ω' γ' σ) →ₗ[ℝ]
                   BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             0 ≤ f → 0 ≤ P' σ τ hστ f) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
             P' σ τ hστ (1 : BoundedBorel (EvolutionState Ω' γ' τ)) ≤
               (1 : BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
             P' σ τ (hσr.trans hrτ) =
               (P' σ r hσr).comp (P' r τ hrτ)) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (p : EvolutionState Ω' γ' σ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             P' σ τ hστ f p =
               ∫ q, f q ∂(K'.fiberKernel
                 (measurableSet_of_isAdmissibleEvolutionDomain hΩ')
                 σ τ hστ p)) ∧
           MovingFiberKernel.HasEndpoint K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') ∧
           MovingFiberKernel.HasComposition K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') →
          MovingFiberKernel.IsZeroExtensionDominatedBy K' K hsub) ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n),
              B σ y z = B σ y z'),
          ∃ Q : ParabolicOperatorFamily Ω γ,
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
                (y : EvolutionPosition Ω γ σ) (z : PDE.Vec n),
              parabolicMarginalKernel K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ τ hστ y =
                K.fiberFirstMarginal
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ τ hστ (evolutionStateOfPosition Ω γ σ y z)) ∧
            (∀ (σ : ℝ),
              Q σ σ le_rfl =
                (LinearMap.id :
                  BoundedBorel (EvolutionPosition Ω γ σ) →ₗ[ℝ]
                    BoundedBorel (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ : ℝ) (τ : ℝ) (hστ : σ ≤ τ)
                (f : BoundedBorel (EvolutionPosition Ω γ τ)),
              0 ≤ f → 0 ≤ Q σ τ hστ f) ∧
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
              Q σ τ hστ (1 : BoundedBorel (EvolutionPosition Ω γ τ)) ≤
                (1 : BoundedBorel (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
              Q σ τ (hσr.trans hrτ) =
                (Q σ r hσr).comp (Q r τ hrτ)) ∧
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
                (y : EvolutionPosition Ω γ σ)
                (f : BoundedBorel (EvolutionPosition Ω γ τ)),
              Q σ τ hστ f y =
                ∫ y', f y' ∂(parabolicMarginalKernel K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ τ hστ y)) ∧
            (∀ (E : Set (PDE.Vec n)) (hE : MeasurableSet E),
              Measurable (fun q : ParabolicEvolutionQuery Ω γ =>
                parabolicMarginalAmbientMeasure K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ) q E)) ∧
            (∀ (σ : ℝ),
              parabolicMarginalKernel K
                (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                σ σ le_rfl =
                (ProbabilityTheory.Kernel.id :
                  ProbabilityTheory.Kernel
                    (EvolutionPosition Ω γ σ) (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
              parabolicMarginalKernel K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ τ (hσr.trans hrτ) =
                parabolicMarginalKernel K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  r τ hrτ ∘ₖ
                parabolicMarginalKernel K
                  (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
                  σ r hσr) ∧
            (∀ (τ : ℝ) (F : BoundedBorel (PDE.Vec n)),
              ParabolicProbe.IsSmoothCompactScalarTerminalDatum
                  Ω γ τ F →
                ∃ V : TimeVelocity n → ℝ,
                  ParabolicProbe.IsClassicalScalarTerminalSolution
                    Ω γ B τ F V ∧
                  (∀ (σ : ℝ) (hστ : σ ≤ τ)
                      (y : EvolutionPosition Ω γ σ),
                    V (σ, y.1) =
                      Q σ τ hστ (terminalPositionDatum F) y) ∧
                  (∀ W : TimeVelocity n → ℝ,
                    ParabolicProbe.IsClassicalScalarTerminalSolution
                      Ω γ B τ F W →
                      EqOn W V
                        (ParabolicProbe.scalarPastClosedCylinder Ω γ τ)))) := by
  exact HypoellipticAleksandrov.KineticAleksandrov.exists_terminalEvolution_proof
    n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
    hb_lipschitz hb_coercive

end HypoellipticAleksandrov.KineticAleksandrov
