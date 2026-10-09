module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator

/-!
# Classical representation of the terminal integral operators

The same classical solution chosen from `hEx` represents all earlier point evaluations.
This is the shared-witness clause of the shared witness, independent of kernel composition.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set

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

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The integral operator agrees with the characterized smooth terminal point value. -/
theorem terminalOperators_apply_smooth
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    P₀ σ τ hστ (terminalStateDatum F) p =
      terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ τ hστ p F hF := by
  let q := evolutionQueryOfState Ω γ σ τ hστ p
  rw [terminalOperators_apply, terminalFiberKernel_apply]
  have hc := comap_terminalMeasure_eq_rieszMeasure n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q
  dsimp only [q, evolutionQueryOfState] at hc
  have hi := congrArg (fun ν : Measure (EvolutionState Ω γ τ) =>
    ∫ x, terminalStateDatum F x ∂ν) hc
  apply hi.trans
  have hmap := terminalMeasure_eq_map_rieszMeasure n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q
  have hint := (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).2.2 F hF
  rw [hmap, (MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ))).integral_map] at hint
  exact hint

/-- One classical solution represents every evaluation of the operator family. -/
theorem terminalOperators_classical
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ σ hστ (p : EvolutionState Ω γ σ),
        u ⟨σ, p.1.1, p.1.2⟩ = P₀ σ τ hστ (terminalStateDatum F) p) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
  obtain ⟨u, hu, _, huniq⟩ := hEx τ F hF
  refine ⟨u, hu, ?_, huniq⟩
  intro σ hστ p
  rw [terminalOperators_apply_smooth]
  exact (terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    σ τ hστ p F hF u hu).symm

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
