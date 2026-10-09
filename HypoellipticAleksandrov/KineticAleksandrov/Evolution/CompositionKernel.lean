module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTrace
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Kernel composition and composition on bounded Borel data

The composed measure is characterized by the terminal measures, using composition on smooth compact
probes. All equalities hold at every source state.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ProbabilityTheory ENNReal

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

/-- The terminal fiber kernels satisfy pointwise composition. -/
theorem terminalFiberKernel_comp
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr := by
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ
  apply ProbabilityTheory.Kernel.ext
  intro p
  let q := evolutionQueryOfState Ω γ σ τ (hσr.trans hrτ) p
  let ν := (κ r τ hrτ ∘ₖ κ σ r hσr) p
  let νa := ν.map ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
  have hmass : νa univ ≤ 1 := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
    change (κ r τ hrτ ∘ₖ κ σ r hσr) p univ ≤ 1
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ MeasurableSet.univ]
    calc
      (∫⁻ x, κ r τ hrτ x univ ∂(κ σ r hσr p)) ≤ ∫⁻ _x, 1 ∂(κ σ r hσr p) :=
        lintegral_mono fun x => terminalFiberKernel_univ_le_one n hn lam Lam m L_b
          hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
          hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ x
      _ = κ σ r hσr p univ := by rw [lintegral_const, one_mul]
      _ ≤ 1 := terminalFiberKernel_univ_le_one n hn lam Lam m L_b
        hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
        hb_smooth hb_lipschitz hb_coercive hEx σ r hσr p
  have hsupp : νa.restrict (evolutionStateSet Ω γ τ) = νa :=
    map_subtype_val_restrict (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ)) ν
  have hint (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
      (∫ x, F x ∂νa) = terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ τ (hσr.trans hrτ) p F hF := by
    rw [(MeasurableEmbedding.subtype_coe
      (measurableSet_evolutionStateSet_of_isOpen
        (isOpen_of_isAdmissibleEvolutionDomain hΩ))).integral_map]
    change (∫ x, terminalStateDatum F x ∂((κ r τ hrτ ∘ₖ κ σ r hσr) p)) = _
    rw [ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel (terminalStateDatum F) _)]
    simp_rw [← terminalOperators_apply]
    have hc := congrArg (fun f : BoundedBorel (EvolutionState Ω γ σ) => f p)
      (terminalOperators_comp_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ r τ hσr hrτ F hF)
    rw [← hc]
    exact terminalOperators_apply_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      σ τ (hσr.trans hrτ) p F hF
  have heq := terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    q νa hmass hsupp hint
  have hm := congrArg (Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)) heq
  rw [(MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ))).comap_map] at hm
  exact hm.symm

/-- The terminal operators compose on every bounded Borel datum. -/
theorem terminalOperators_comp
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ) := by
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [terminalOperators_apply, terminalFiberKernel_comp n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r τ hσr hrτ,
    ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel f _)]
  change _ = P₀ σ r hσr (P₀ r τ hrτ f) p
  rw [terminalOperators_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      r τ hrτ f x).symm)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
