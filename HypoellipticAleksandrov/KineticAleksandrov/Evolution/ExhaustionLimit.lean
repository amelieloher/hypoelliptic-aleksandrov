module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBalls
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitInterval
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeSpace

/-!
# Actual classical viscous terminal evolution by exhaustion

For every source-admissible domain, the actual finite Dirichlet construction,
proved comparison estimates, locally uniform convergence, compact-test passage,
Hörmander regularity, boundary continuity and finite-past gluing yield the literal
classical terminal-solution predicate with the original bound and uniqueness.

Classical Dirichlet solvability (Lieberman, Theorem 5.14) and Hörmander's theorem remain
explicit hypotheses. This is
a classical viscous evolution result relative to those hypotheses.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set
open scoped MatrixOrder

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
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive

/-- **Exhaustion limit.** Actual bounded classical viscous terminal
solutions exist and are unique on every admissible moving domain, relative
only to the two explicit hypotheses. -/
theorem exists_viscous_terminalSolution
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
  rcases hΩ with hWhole | ⟨c, r, hr, hBall⟩ | ⟨hN, lo, hi, hlohi, hInterval⟩
  · rw [hWhole] at hF ⊢
    exact exists_viscous_terminalSolution_wholeSpace hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ
      τ F hF ε hε hε1 C hC hFC
  · rw [hBall] at hF ⊢
    exact exists_viscous_terminalSolution_ball hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ hr
      τ F hF ε hε hε1 C hC hFC
  · exact exists_viscous_terminalSolution_interval hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ
      hN Ω lo hi hlohi hInterval τ F hF ε hε hε1 C hC hFC

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
