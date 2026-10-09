module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1DerivativesFinal

/-! # Uniform integral bounds for the canonical real exit density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- A canonical density with a norm support bound is compactly supported. -/
theorem spatialDensity_hasCompactSupport {d : ℕ} {E : Type} [NormedAddCommGroup E]
    (G : PDE.Vec d → E) (r : ℝ) (hz : ∀ y, r < ‖y‖ → G y = 0) :
    HasCompactSupport G := by
  apply (isCompact_closedBall (0 : PDE.Vec d) r).of_isClosed_subset (isClosed_tsupport G)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hy (hz y (lt_of_not_ge h))

/-- Structural constants bound every derivative integral of the canonical exit density. -/
theorem spatialDensity_uniform_integral_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time = R ^ 2 / 8 → ∀ j,
      (∫ y, ‖iteratedFDeriv ℝ j
        (exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)) y‖) ≤
        C j * R ^ (-3 * (j : ℝ)) := by
  obtain ⟨D, hD, hb⟩ :=
    ballExitL1Inversion_uniform_derivative_bound hH hLE d hd lam Lam hlam hLam
  refine ⟨fun j => (2 : ℝ) ^ d * D j, fun j => mul_nonneg (by positivity) (hD j), ?_⟩
  intro B hB v₀ R hR P T hv hT j
  let G := exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)
  have hbound (y : PDE.Vec d) : ‖iteratedFDeriv ℝ j G y‖ ≤
      D j * R ^ (-3 * ((d : ℝ) + (j : ℝ))) :=
    (ballExitL1Density_derivative_le hH hLE hd hlam hLam B hB v₀ hR P T hv hT j y).trans
      (hb B hB v₀ R hR P T hv hT j y)
  have hi := exitDerivative_integral_le_volume G hR
    (ballExitL1Density_zero_outside hH hLE hd hlam hLam B hB v₀ hR P T hv hT) j
    (mul_nonneg (hD j) (Real.rpow_nonneg hR.le _)) hbound
  have hp : R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ))) =
      R ^ (-3 * (j : ℝ)) := by
    rw [← Real.rpow_natCast R (3 * d), ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((2 : ℝ) ^ d * R ^ (3 * d)) *
        (D j * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) := hi
    _ = ((2 : ℝ) ^ d * D j) *
        (R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) := by ring
    _ = _ := by rw [hp]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
