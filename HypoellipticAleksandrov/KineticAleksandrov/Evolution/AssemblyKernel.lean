module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator

/-! # The master kernel from the characterized terminal measures

The only hypothesis here is the joint measurability of the terminal measures.
Support and mass come from the construction of the terminal measures; the fixed-time fibers
are the same kernels as in `FixedFiberMeasure`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set MeasureTheory
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

/-- The ambient master is literally the family of terminal measures, with joint measurability
supplied explicitly. -/
def constructionTerminalKernel (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
    MovingFiberKernel Ω γ where
  master := ⟨μ, hJoint⟩
  terminal_support q := (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).2.1
  mass_le_one q := (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).1

/-- The master kernel uses the existing characterized measure at every valid query. -/
theorem constructionTerminalKernel_master
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) (q : EvolutionQuery Ω γ) :
    (constructionTerminalKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      hJoint).master q = μ q := rfl

/-- The fiber identification follows from the identical map/comap constructions. -/
theorem constructionTerminalKernel_fiber_eq
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q))
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    (constructionTerminalKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint).fiberKernel
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ = κ σ τ hστ := by
  apply ProbabilityTheory.Kernel.ext
  intro p
  rw [MovingFiberKernel.fiberKernel_apply, terminalFiberKernel_apply]
  rfl

end EvolutionData
end HypoellipticAleksandrov.KineticAleksandrov
