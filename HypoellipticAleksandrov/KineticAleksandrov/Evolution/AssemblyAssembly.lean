module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.AssemblyKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovariance
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDomination
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion

/-! # Clause-by-clause assembly of the terminal evolution

Every clause is assembled for the same integral operators and the same characterized
master measures. Composition and joint measurability remain explicit premises.
This module performs no analytic limit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory SectionTwo
open scoped ProbabilityTheory

section EvolutionData
variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Assemble every conjunct using one operator and one master-kernel witness.
The premises are the composition identity and the joint measurability of the master kernel;
the marginal package is consumed directly. -/
theorem construction_terminalEvolution_assembly
    (hH : HormanderHypoellipticityStatement)
    (hComp : ∀ σ r τ hσr hrτ,
      P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ))
    (hKComp : ∀ σ r τ hσr hrτ,
      κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr)
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
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
          let _ := hE
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
          let _ := hBz
          IsTranslationCovariantEvolution Ω γ
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
        IsDomainMonotoneEvolution Ω γ B b K ∧
        HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K
 := by
  let K := constructionTerminalKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint
  have hK (q : EvolutionQuery Ω γ) : K.master q = μ q := rfl
  have hFiber (σ τ : ℝ) (hστ : σ ≤ τ) :
      K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ =
        κ σ τ hστ :=
    constructionTerminalKernel_fiber_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint σ τ hστ
  have hComposition : K.HasComposition
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) := by
    intro σ r τ hσr hrτ
    rw [hFiber, hFiber, hFiber]
    exact hKComp σ r τ hσr hrτ
  have hBasic := terminalOperators_basic n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
  refine ⟨P₀, K, ?_, hBasic.1, hBasic.2.1, hBasic.2.2.1, ?_, ?_,
    K.terminal_support, K.mass_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact terminalOperators_classical n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
  · exact hComp
  · intro σ τ hστ p f
    rw [hFiber]
    exact terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ f p
  · exact K.jointlyMeasurable_apply
  · exact K.fiberKernel_mass_le_one (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
  · intro σ
    rw [hFiber]
    exact hBasic.2.2.2 σ
  · exact hComposition
  · exact terminalKernel_translation_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK
  · exact terminalKernel_domain_domination_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK
  · exact terminalMarginal_properties_of_master_eq n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
      hb_lipschitz hb_coercive hEx hH K hK hComposition

end EvolutionData
end HypoellipticAleksandrov.KineticAleksandrov
