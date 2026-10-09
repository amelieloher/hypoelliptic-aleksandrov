module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceComparison
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Composition on smooth compact terminal data

Compact intermediate approximants have uniformly bounded data. Weighted comparison
identifies their solution values with the original solution; dominated convergence
identifies their integrals with the integral of the original intermediate trace.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology

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

local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal integral operators compose on smooth compact terminal data. -/
theorem terminalOperators_comp_smooth
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    P₀ σ τ (hσr.trans hrτ) (terminalStateDatum F) =
      P₀ σ r hσr (P₀ r τ hrτ (terminalStateDatum F)) := by
  have hself (t : ℝ) := (terminalOperators_basic n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx).1 t
  by_cases heq : r = τ
  · subst τ
    rw [hself]
    rfl
  have hrt : r < τ := lt_of_le_of_ne hrτ heq
  obtain ⟨C, hC0, hCF⟩ := F.exists_bound
  obtain ⟨u, hu, hCu, _⟩ := hEx τ F hF
  have hC := hCu C hC0 hCF
  have hrep (s : ℝ) (hst : s ≤ τ) (p : EvolutionState Ω γ s) :
      P₀ s τ hst (terminalStateDatum F) p = u ⟨s, p.1.1, p.1.2⟩ := by
    rw [terminalOperators_apply_smooth]
    exact terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      s τ hst p F hF u hu
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (j : ℕ) := hu.exists_compact_slice_approximation
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hrt hC0 hC (hε j)
  choose G hG hGC hGerr using hex
  have hvex (j : ℕ) := hEx r (G j) (hG j)
  choose v hv hvbound hvuniq using hvex
  have herr (j : ℕ) (p : KineticPoint n) (hp : p ∈ evolutionPastClosedCylinder Ω γ r) :
      |u p - v j p| ≤ ε j *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) L_b) r p := by
    apply classical_intermediate_abs_sub_le_growth
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hlam hB_ell hb_lipschitz
      hrτ (hε j).le hu (hv j) ?_ p hp
    intro q hq
    rw [(hv j).2.2.2.2.1 q hq]
    exact hGerr j q hq
  apply BoundedBorel.ext
  intro p
  have hp : (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n) ∈
      evolutionPastClosedCylinder Ω γ r := mk_mem_evolutionPastClosedCylinder hσr p
  have hvalues : Tendsto (fun j => v j ⟨σ, p.1.1, p.1.2⟩) atTop
      (𝓝 (u ⟨σ, p.1.1, p.1.2⟩)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs, abs_sub_comm]
    apply squeeze_zero (fun j => abs_nonneg _) (fun j => herr j _ hp)
    simpa only [zero_mul] using hεlim.mul_const
      (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) L_b)
        r (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n))
  have hpoint (x : EvolutionState Ω γ r) :
      Tendsto (fun j => G j x.1) atTop (𝓝 (u ⟨r, x.1.1, x.1.2⟩)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs, abs_sub_comm]
    apply squeeze_zero (fun j => abs_nonneg _)
      (fun j => hGerr j ⟨r, x.1.1, x.1.2⟩ ⟨rfl, subset_closure x.2.1⟩)
    simpa only [zero_mul] using hεlim.mul_const
      (1 + radialSq (⟨r, x.1.1, x.1.2⟩ : KineticPoint n))
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have hint := tendsto_integral_of_dominated_convergence (μ := κ σ r hσr p)
    (fun _ => C)
    (fun j => ((G j).measurable.comp measurable_subtype_coe).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hGC j x.1)
    (Eventually.of_forall hpoint)
  have hlim : Tendsto (fun j => v j ⟨σ, p.1.1, p.1.2⟩) atTop
      (𝓝 (∫ x : EvolutionState Ω γ r, u ⟨r, x.1.1, x.1.2⟩ ∂(κ σ r hσr p))) := by
    have heval (j : ℕ) : v j ⟨σ, p.1.1, p.1.2⟩ =
        ∫ x : EvolutionState Ω γ r, G j x.1 ∂(κ σ r hσr p) := by
      rw [← terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ r hσr p (G j) (hG j) (v j) (hv j), ← terminalOperators_apply_smooth,
        terminalOperators_apply]
      rfl
    simpa only [heval, Function.comp_apply] using hint
  rw [hrep, terminalOperators_apply]
  have heq := tendsto_nhds_unique hvalues hlim
  exact heq.trans (integral_congr_ae (Eventually.of_forall fun x => (hrep r hrτ x).symm))

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
