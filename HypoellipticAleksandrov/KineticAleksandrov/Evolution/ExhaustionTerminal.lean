module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalGeometry

/-!
# Uniform terminal comparison for actual finite Dirichlet solutions

The constant M is chosen before all curves, radii and finite domains. The core comparison
premises are discharged by the global generator bound and the proved support window.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- A common terminal comparison constant exists for every actual finite ellipsoid
solution, uniformly over positive truncation radii satisfying the explicit support margin. -/
theorem exists_uniform_straightened_dirichlet_terminal_bound
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : EvolutionAmbientState n → ℝ))
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a α τ r R d Z L ε : ℝ), a < α →
      0 < r → 0 < R → 0 < d → 0 ≤ L → 0 ≤ ε → ε ≤ 1 →
      ∀ (g : ℝ → PDE.Vec n), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|) →
      (∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
        2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ)) →
      (∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ), PDE.vecEuclideanNorm q.2 ≤ Z) →
      (r - d) ^ 2 / r ^ 2 + Z ^ 2 / R ^ 2 < 1 → τ - d / (1 + L) ≤ α →
      ∀ u : TimeVelocity (n + n) → ℝ,
      IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n r R))
        (straightenedCoefficient B g ε) (straightenedDrift b g)
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u →
      ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
        (openEllipsoid (straightenedEllipsoidMatrix n r R)),
        |straightenedPullback g u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  obtain ⟨M, hM⟩ := exists_terminalGenerator_bound hF hFc hlam hB hb
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro a α τ r R d Z L ε haα hr hR hd hL hε hε1 g hg hgL hs hsZ hsize hwin u hu
  apply abs_sub_terminalDatum_le_straightened_dirichlet_core
    (isOpen_straightenedEllipsoid n hr hR) (isBounded_straightenedEllipsoid n hr hR)
    hlam hB haα hε (le_max_right M 0) hg F hF
    (fun p => (hM ε hε hε1 p).trans (le_max_left M 0)) ?_ u hu
  intro p hp
  exact terminalDatum_eq_zero_on_straightened_lateral_window
    hr hR hd hL hgL hs hsZ hsize hp.1.2 (hwin.trans hp.1.1) hp.2

end HypoellipticAleksandrov.KineticAleksandrov
