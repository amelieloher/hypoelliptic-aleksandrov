module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationComparison

/-!
# Domination of every smaller admissible evolution by the terminal kernel

Companion paper, Proposition 2.1 (domain covariance), domination half.  Let `(Ω', γ')` be an
admissible moving subdomain of `(Ω, γ)` and let `(P', K')` be ANY terminal operator family and
moving fiber kernel for `(Ω', γ')` satisfying the full eight-clause antecedent of the
fourteenth conjunct.  Then the master measures of `K'` are dominated by those of the terminal
family `μ` of terminal measures on the large domain.

Proof: for nonnegative smooth compact data `F` in the small terminal fiber, clauses 1 and 6 give
`∫ F dK'.master q' = u'(σ, p')` for the small classical solution `u'`; the large solution
`u` satisfies `∫ F dμ q = u(σ, p')`; `classical_le_of_subdomain` gives `u' ≤ u`.
The smooth-probe domination criterion `measure_le_of_smooth_integral_le` upgrades the integral
inequalities to the measure inequality.  Clauses 2–5, 7, 8 of the antecedent are kept in the
statement (they are part of the conjunct) but are not needed.

* `terminalMeasure_domination`: the measure inequality from clauses 1 and 6 only.
* `terminalKernel_domain_domination_of_master_eq`: the domain domination statement for every `K`
  with `K.master q = μ q`; the master kernel `K₀` is such a kernel by definition.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section Outside

variable {n : ℕ}

/-- Clause 6 of the antecedent identifies the integral of a terminal datum against the master
measure of a query with the `P'` value of the restricted datum. -/
theorem integral_master_eq_operator {Ω' : Set (PDE.Vec n)} {γ' : ℝ → PDE.Vec n}
    (hΩ' : IsAdmissibleEvolutionDomain Ω') (K' : MovingFiberKernel Ω' γ')
    (P' : TerminalOperatorFamily Ω' γ') {τ : ℝ}
    (h6 : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ)
      (f : BoundedBorel (EvolutionState Ω' γ' τ)),
        P' σ τ hστ f p = ∫ q, f q ∂(K'.fiberKernel
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p))
    (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ)
    (F : BoundedBorel (EvolutionAmbientState n)) :
    P' σ τ hστ (terminalStateDatum F) p =
      ∫ x, F x ∂(K'.master (evolutionQueryOfState Ω' γ' σ τ hστ p)) := by
  rw [h6 σ τ hστ p (terminalStateDatum F),
    ← MovingFiberKernel.map_fiberKernel_eq_master K'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p,
    integral_map measurable_subtype_coe.aemeasurable F.measurable.aestronglyMeasurable]
  rfl

end Outside

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "S" => terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Domain domination at the level of master measures, from clauses 1 and 6 of the antecedent only:
the master measure of ANY small kernel `K'` with the clause-1 solution representation and the
clause-6 operator integral is dominated by the terminal measure of the corresponding large query. -/
theorem terminalMeasure_domination
    (Ω' : Set (PDE.Vec n)) (γ' : ℝ → PDE.Vec n)
    (hΩ' : IsAdmissibleEvolutionDomain Ω') (hγ' : IsContinuousPiecewiseC1 γ')
    (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆ movingDomain Ω γ σ)
    (P' : TerminalOperatorFamily Ω' γ') (K' : MovingFiberKernel Ω' γ')
    (h1 : ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
      IsSmoothCompactTerminalDatum Ω' γ' τ F →
        ∃ u : KineticPoint n → ℝ,
          IsClassicalTerminalSolution Ω' γ' B b τ F u ∧
          (∀ (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ),
            u ⟨σ, p.1.1, p.1.2⟩ = P' σ τ hστ (terminalStateDatum F) p) ∧
          (∀ v : KineticPoint n → ℝ,
            IsClassicalTerminalSolution Ω' γ' B b τ F v →
              EqOn v u (evolutionPastClosedCylinder Ω' γ' τ)))
    (h6 : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ)
      (f : BoundedBorel (EvolutionState Ω' γ' τ)),
        P' σ τ hστ f p = ∫ q, f q ∂(K'.fiberKernel
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p))
    (q' : EvolutionQuery Ω' γ') :
    K'.master q' ≤ μ (largeQueryOfSmall hsub q') := by
  obtain ⟨⟨σ, τ, w⟩, hστ, hw⟩ := q'
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  have hΩo' := isOpen_of_isAdmissibleEvolutionDomain hΩ'
  have hU : IsOpen (evolutionStateSet Ω' γ' τ) := (isOpen_movingDomain hΩo' τ).prod isOpen_univ
  have hspec := terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (largeQueryOfSmall hsub ⟨(σ, τ, w), hστ, hw⟩)
  have hfinν : IsFiniteMeasure (K'.master ⟨(σ, τ, w), hστ, hw⟩) :=
    ⟨(K'.mass_le_one ⟨(σ, τ, w), hστ, hw⟩).trans_lt ENNReal.one_lt_top⟩
  have hfinμ : IsFiniteMeasure (μ (largeQueryOfSmall hsub ⟨(σ, τ, w), hστ, hw⟩)) :=
    ⟨hspec.1.trans_lt ENNReal.one_lt_top⟩
  refine measure_le_of_smooth_integral_le hU (K'.terminal_support ⟨(σ, τ, w), hστ, hw⟩) ?_
  intro f hfs hfc hfU hfnn
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hfs.continuous
  let F : BoundedBorel (EvolutionAmbientState n) :=
    ⟨f, hfs.continuous.measurable, ⟨max C 0, le_max_right _ _,
      fun x => (hC x).trans (le_max_left _ _)⟩⟩
  have hF' : IsSmoothCompactTerminalDatum Ω' γ' τ F := ⟨hfs, hfc, hfU⟩
  have hF : IsSmoothCompactTerminalDatum Ω γ τ F :=
    ⟨hfs, hfc, hfU.trans fun x hx => ⟨hsub τ hx.1, mem_univ _⟩⟩
  obtain ⟨u', hu', hrep, -⟩ := h1 τ F hF'
  obtain ⟨u, hu, -, -⟩ := hEx τ F hF
  have hcmp := classical_le_of_subdomain hΩo hΩo' hγ.1 hγ'.1 hsub hlam hB_ell hb_lipschitz
    hu hu' hfnn ⟨σ, w.1, w.2⟩ ⟨hστ, subset_closure hw.1⟩
  have hA := integral_master_eq_operator hΩ' K' P' h6 σ hστ ⟨w, hw⟩ F
  have hlhs : ∫ x, f x ∂(K'.master ⟨(σ, τ, w), hστ, hw⟩) = u' ⟨σ, w.1, w.2⟩ :=
    ((hrep σ hστ ⟨w, hw⟩).trans hA).symm
  have hS := terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
    ⟨w, ⟨hsub σ hw.1, hw.2⟩⟩ F hF u hu
  have hrhs : ∫ x, f x ∂(μ (largeQueryOfSmall hsub ⟨(σ, τ, w), hστ, hw⟩)) =
      u ⟨σ, w.1, w.2⟩ := (hspec.2.2 F hF).trans hS
  rw [hlhs, hrhs]
  exact hcmp

/-- Domain domination for every moving fiber kernel `K` whose master measures are the
terminal measures `μ q` (the master kernel `K₀` is such a kernel by definition): ANY
smaller admissible problem `(Ω', γ', P', K')` satisfying the complete eight-clause antecedent of
the fourteenth conjunct is zero-extension dominated by `K`. -/
theorem terminalKernel_domain_domination_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) :
    ∀ (Ω' : Set (PDE.Vec n)) (γ' : ℝ → PDE.Vec n)
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
          MovingFiberKernel.IsZeroExtensionDominatedBy K' K hsub := by
  rintro Ω' γ' hΩ' hγ' hsub P' K' ⟨h1, -, -, -, -, h6, -, -⟩ q'
  rw [hK]
  exact terminalMeasure_domination n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    Ω' γ' hΩ' hγ' hsub P' K' h1 h6 q'

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
