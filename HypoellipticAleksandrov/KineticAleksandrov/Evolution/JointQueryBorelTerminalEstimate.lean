module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal

/-!
# Terminal-time error for fixed compact probes

A fixed smooth compact datum has one global generator bound. On every short slab where
it vanishes on the lateral boundary, composition propagates the terminal barrier error
to all earlier sources. No bound uniform over arbitrary terminal data is asserted.
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

local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- A fixed smooth compact probe has a uniform terminal-time error on every slab
where it vanishes on the lateral frontier. -/
theorem terminalOperators_terminal_time_error
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (q : ℝ) (hτq : τ ≤ q)
      (hFq : IsSmoothCompactTerminalDatum Ω γ q F),
      (∀ z ∈ movingClosedSlab Ω γ τ q,
        z.position ∈ frontier (movingDomain Ω γ z.time) →
          F (z.position, z.velocity) = 0) →
      ∀ (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ),
        |P₀ σ q (hστ.trans hτq) (terminalStateDatum F) p -
          P₀ σ τ hστ (terminalStateDatum F) p| ≤ (q - τ) * M := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_terminalDatum_operator_bound
    hlam hB_ell hb_lipschitz τ F hF
  refine ⟨M, hM0, ?_⟩
  intro q hτq hFq hlat σ hστ p
  obtain ⟨u, hu, hrep, _⟩ := terminalOperators_classical n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q F hFq
  obtain ⟨C, _, hC⟩ := F.exists_bound
  have herr (x : EvolutionState Ω γ τ) :
      |P₀ τ q hτq (terminalStateDatum F) x - terminalStateDatum F x| ≤ (q - τ) * M := by
    rw [← hrep τ hτq x]
    exact classical_sub_terminalDatum_le_core_of_slab
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hlam hB_ell hb_lipschitz
      (le_refl 0) zero_le_one hF.1 hC (fun z _ => hM 0 (le_refl 0) zero_le_one z)
      ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b q F u).2 hu)
      hlat ⟨τ, x.1.1, x.1.2⟩ ⟨le_rfl, hτq, subset_closure x.2.1⟩
  let D := P₀ τ q hτq (terminalStateDatum F) - terminalStateDatum F
  have heq : P₀ σ q (hστ.trans hτq) (terminalStateDatum F) p -
      P₀ σ τ hστ (terminalStateDatum F) p = P₀ σ τ hστ D p := by
    rw [terminalOperators_comp_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      σ τ q hστ hτq F hFq]
    exact (congrArg (fun f : BoundedBorel (EvolutionState Ω γ σ) => f p)
      ((P₀ σ τ hστ).map_sub (P₀ τ q hτq (terminalStateDatum F))
        (terminalStateDatum F))).symm
  rw [heq, terminalOperators_apply]
  exact abs_integral_boundedBorel_le D _
    (terminalFiberKernel_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p)
    (mul_nonneg (sub_nonneg.mpr hτq) hM0) herr

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
