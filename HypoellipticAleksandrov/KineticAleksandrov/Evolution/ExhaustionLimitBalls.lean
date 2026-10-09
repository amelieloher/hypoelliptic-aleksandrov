module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBall

/-! # The full moving-ball branch of the exhaustion limit, including arbitrary centres -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

private theorem piecewiseC1_add_const {n : ℕ} {Γ : ℝ → PDE.Vec n}
    (hΓ : IsContinuousPiecewiseC1 Γ) (c : PDE.Vec n) :
    IsContinuousPiecewiseC1 (fun t => Γ t + c) := by
  refine ⟨hΓ.1.add continuous_const, fun a b hab => ?_⟩
  obtain ⟨N, t, ht, h0, hl, hpiece⟩ := hΓ.2 a b hab
  exact ⟨N, t, ht, h0, hl, fun i => (hpiece i).add contDiffOn_const⟩

/-- A moving ball with centre c is the zero-centred ball moved by the curve Γ + c. -/
theorem movingDomain_ball_add_const {n : ℕ} (c : PDE.Vec n) (r0 : ℝ)
    (Γ : ℝ → PDE.Vec n) (σ : ℝ) :
    movingDomain (PDE.euclideanBall c r0) Γ σ =
      movingDomain (PDE.euclideanBall 0 r0) (fun s => Γ s + c) σ := by
  ext y
  simp only [mem_movingDomain_euclideanBall_iff, add_zero]

/-- Moving the constant ball centre into the centre curve preserves the entire
classical viscous terminal-solution predicate, with coefficients and operator unchanged. -/
theorem isClassicalViscousTerminalSolution_ball_add_const_iff {n : ℕ}
    (c : PDE.Vec n) (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) (v : KineticPoint n → ℝ) :
    IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F v ↔
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0)
        (fun s => Γ s + c) B b ε τ F v := by
  simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
    evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
    evolutionLateralFrontier, movingDomain_ball_add_const c r0 Γ]

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {c : PDE.Vec n}
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) {r0 : ℝ} (hr0 : 0 < r0)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ hr0

/-- The ball branch of the exhaustion limit with arbitrary centre: actual bounded classical
viscous evolution and uniqueness, relative to explicit Lieberman and Hörmander inputs. -/
theorem exists_viscous_terminalSolution_ball
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ)) := by
  have hF0 : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0)
      (fun s => Γ s + c) τ F := by
    simpa only [IsSmoothCompactTerminalDatum, evolutionStateSet,
      movingDomain_ball_add_const c r0 Γ] using hF
  obtain ⟨v, hv, hbound, huniq⟩ := exists_viscous_terminalSolution_innerBall
    hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco (piecewiseC1_add_const hΓ c) hr0
    τ F hF0 ε hε hε1 C hC hFC
  have hK : evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ =
      evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) (fun s => Γ s + c) τ := by
    simp only [evolutionPastClosedCylinder, movingDomain_ball_add_const c r0 Γ]
  refine ⟨v, (isClassicalViscousTerminalSolution_ball_add_const_iff
    c r0 Γ B b ε τ F v).mpr hv, ?_, ?_⟩
  · simpa only [hK] using hbound
  · intro w hw
    have hw0 := (isClassicalViscousTerminalSolution_ball_add_const_iff
      c r0 Γ B b ε τ F w).mp hw
    simpa only [hK] using huniq w hw0

end Data

end HypoellipticAleksandrov.KineticAleksandrov
