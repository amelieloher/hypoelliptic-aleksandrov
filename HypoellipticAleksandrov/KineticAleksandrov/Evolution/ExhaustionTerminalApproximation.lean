module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# A terminal-window bound uniform in the inner-ball approximation index

Both constants and the transported-radius threshold are chosen before the approximation
error and curve. All support and radius premises of the finite-domain core are discharged.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- Decreasing the diffused radius improves the relative collar-gap condition. -/
theorem terminal_window_ratio_le_of_radius_le {r r0 d : ℝ} (hr : 0 < r)
    (hdr : d < r) (hd : 0 ≤ d) (hrr0 : r ≤ r0) :
    (r - d) ^ 2 / r ^ 2 ≤ (r0 - d) ^ 2 / r0 ^ 2 := by
  have hr0 : 0 < r0 := hr.trans_le hrr0
  have hf := div_le_div_of_nonneg_left hd hr hrr0
  have hl : 0 ≤ 1 - d / r := sub_nonneg.mpr ((div_le_one hr).mpr hdr.le)
  have hm : 1 - d / r ≤ 1 - d / r0 := by linarith
  have hs := pow_le_pow_left₀ hl hm 2
  simpa only [← div_pow, sub_div, div_self hr.ne', div_self hr0.ne'] using hs

/-- The actual approximation solutions have one common terminal-window bound and one
transported cutoff threshold. Neither depends on the approximation curve or index. -/
theorem exists_uniform_innerBall_dirichlet_terminal_bound
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {τ r0 d L : ℝ} (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L)
    {Γ : ℝ → PDE.Vec n}
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : EvolutionAmbientState n → ℝ))
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ))
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) :
    ∃ M R0 : ℝ, 0 ≤ M ∧ 0 < R0 ∧ ∀ (a α β R ε : ℝ), a < α →
      0 ≤ β → β ≤ d → R0 ≤ R → 0 ≤ ε → ε ≤ 1 → τ - d / (1 + L) ≤ α →
      ∀ g : ℝ → PDE.Vec n, ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|) →
      PDE.vecEuclideanNorm (g τ - Γ τ) ≤ β / 2 →
      ∀ u : TimeVelocity (n + n) → ℝ,
      IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β) R))
        (straightenedCoefficient B g ε) (straightenedDrift b g)
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u →
      ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β) R)),
        |straightenedPullback g u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_straightened_dirichlet_terminal_bound hlam hB hb F hF hFc
  obtain ⟨Z, -, hZ⟩ := exists_transported_terminal_support_bound hFc
  obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_terminal_window
    (by linarith : 0 < r0) hd (by linarith : d < r0) Z
  refine ⟨M, R0, hM0, hR0, ?_⟩
  intro a α β R ε haα hβ hβd hR hε hε1 hwin g hg hgL hc u hu p hp
  have hr : 0 < r0 - β := by linarith
  have hdr' : d < r0 - β := by linarith
  have hs := terminal_support_margin_of_innerBall_close hβd hsupp hc
  have hrsize : (r0 - β - d) ^ 2 / (r0 - β) ^ 2 + Z ^ 2 / R ^ 2 < 1 :=
    lt_of_le_of_lt
      (add_le_add (terminal_window_ratio_le_of_radius_le hr hdr' hd.le (by linarith))
        (le_refl _)) (hsize R hR)
  exact hM a α τ (r0 - β) R d Z L ε haα hr (hR0.trans_le hR) hd hL hε hε1 g hg hgL
    hs hZ hrsize hwin u hu p hp

end HypoellipticAleksandrov.KineticAleksandrov
