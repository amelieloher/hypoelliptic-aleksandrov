module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBalls
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry

/-! # The bounded one-dimensional interval branch of the exhaustion limit -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ

/-- The interval branch of the exhaustion limit follows from its exact Euclidean-ball
identification, with the source constants, operator and terminal datum preserved. -/
theorem exists_viscous_terminalSolution_interval
    (hN : n = 1) (Ω : Set (PDE.Vec n)) (lo hi : ℝ) (hlohi : lo < hi)
    (hΩ : hN ▸ Ω = PDE.oneDimensionalAxisBox lo hi)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution Ω Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder Ω Γ τ)) := by
  cases hN
  have hΩ' : Ω = PDE.oneDimensionalAxisBox lo hi := by simpa using hΩ
  rw [hΩ', oneDimensionalAxisBox_eq_euclideanBall hlohi] at hF ⊢
  exact exists_viscous_terminalSolution_ball hLE hH hn hlam hlamLam hm hmLb
    hBs hBsym hB hbs hb hbco hΓ (show 0 < (hi - lo) / 2 by linarith)
    τ F hF ε hε hε1 C hC hFC

end Data

end HypoellipticAleksandrov.KineticAleksandrov
