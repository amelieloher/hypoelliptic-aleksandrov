module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1DerivativesReal
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1DerivativesSupport

/-! # The exact joint-witness smooth position-density surface for local ball exit -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The actual exit measure has one smooth `L¹` density with every raw derivative estimate. -/
theorem ballExit_smooth_position_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C_m : ℕ → ℝ, (∀ j, 0 ≤ C_m j) ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time = R ^ 2 / 8 →
      let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
      ∃ (g : PDE.Vec d × TimeVelocity d → ℝ)
        (G : PDE.Vec d → Lp ℂ 1 (ν.map Prod.snd)),
        Measurable g ∧
        ν = (volume.prod (ν.map Prod.snd)).withDensity
          (fun z => ENNReal.ofReal (g z)) ∧
        (∀ y, (G y : TimeVelocity d → ℂ) =ᵐ[ν.map Prod.snd]
          fun z => (g (y, z) : ℂ)) ∧
        ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ j : ℕ, 1 ≤ j →
          (∀ y, ‖iteratedFDeriv ℝ j G y‖ ≤
            C_m j * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) ∧
          (∫ y, ‖iteratedFDeriv ℝ j G y‖) ≤ C_m j * R ^ (-3 * (j : ℝ)) := by
  obtain ⟨D, hD, hb⟩ :=
    ballExitL1Inversion_uniform_derivative_bound hH hLE d hd lam Lam hlam hLam
  let C_m (j : ℕ) := D j * ((2 : ℝ) ^ d + 1)
  have htwo : 0 ≤ (2 : ℝ) ^ d := by positivity
  have hC (j : ℕ) : 0 ≤ C_m j := mul_nonneg (hD j) (by positivity)
  refine ⟨C_m, hC, ?_⟩
  intro B hB v₀ R hR P T hv hT
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let G := exitL1Density ν
  refine ⟨exitJointDensity ν, G, measurable_exitJointDensity ν,
    ballExit_eq_withDensity_exitJointDensity hH hLE hd hlam hLam B hB v₀ hR P T hv hT,
    ballExitL1Density_coe hH hLE hd hlam hLam B hB v₀ hR P T hv hT,
    ballExitL1Density_contDiff hH hLE hd hlam hLam B hB v₀ hR P T hv hT, ?_⟩
  intro j _hj
  have hbound (y : PDE.Vec d) : ‖iteratedFDeriv ℝ j G y‖ ≤
      D j * R ^ (-3 * ((d : ℝ) + (j : ℝ))) :=
    (ballExitL1Density_derivative_le hH hLE hd hlam hLam B hB v₀ hR P T hv hT j y).trans
      (hb B hB v₀ R hR P T hv hT j y)
  have hDC : D j ≤ C_m j := by
    dsimp only [C_m]
    nlinarith [mul_nonneg (hD j) htwo]
  refine ⟨fun y => (hbound y).trans (mul_le_mul_of_nonneg_right hDC
    (Real.rpow_nonneg hR.le _)), ?_⟩
  have hzero := ballExitL1Density_zero_outside hH hLE hd hlam hLam B hB v₀ hR P T hv hT
  have hvb := exitDerivative_integral_le_volume G hR hzero j
    (mul_nonneg (hD j) (Real.rpow_nonneg hR.le _)) hbound
  have hp : R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ))) =
      R ^ (-3 * (j : ℝ)) := by
    rw [← Real.rpow_natCast R (3 * d), ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hscale : ((2 : ℝ) ^ d * R ^ (3 * d)) *
      (D j * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) =
      ((2 : ℝ) ^ d * D j) * R ^ (-3 * (j : ℝ)) := by
    calc
      _ = ((2 : ℝ) ^ d * D j) *
          (R ^ (3 * d) * R ^ (-3 * ((d : ℝ) + (j : ℝ)))) := by ring
      _ = _ := by rw [hp]
  rw [hscale] at hvb
  have hCC : (2 : ℝ) ^ d * D j ≤ C_m j := by
    dsimp only [C_m]
    nlinarith [hD j]
  exact hvb.trans (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hR.le _))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
