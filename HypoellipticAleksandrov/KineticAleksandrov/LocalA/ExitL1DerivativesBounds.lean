module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1Derivatives
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1FourierScaling
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Complex.Basic

/-! # Uniform raw supremum estimates for derivatives of the single inverse -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The actual total-variation bound implies a raw, dimension-sensitive moment estimate. -/
theorem exitL1Fourier_moment_bound {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    {C c R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hR : 0 < R)
    (hdecay : ∀ ξ, ((exitFourier ν ξ).variation univ).toReal ≤
      C * Real.exp (-c * (R ^ 3 * PDE.vecEuclideanNorm ξ) ^ (1 / 3 : ℝ)))
    (j : ℕ) (hi : Integrable (fun ξ => ‖ξ‖ ^ j * ‖exitL1Fourier ν ξ‖)) :
    (∫ ξ, ‖ξ‖ ^ j * ‖exitL1Fourier ν ξ‖) ≤
      C * ((R ^ 3) ^ (d + j))⁻¹ * exitFrequencyMoment (d := d) c j := by
  have hi' := (integrable_exitFrequency_scaled_moment hd j hc hR).const_mul C
  have hb (ξ : PDE.Vec d) : ‖ξ‖ ^ j * ‖exitL1Fourier ν ξ‖ ≤
      C * (‖ξ‖ ^ j * Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ))) := by
    rw [norm_exitL1Fourier]
    have hexp : Real.exp (-c * (R ^ 3 * PDE.vecEuclideanNorm ξ) ^ (1 / 3 : ℝ)) ≤
        Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hc.le)
      apply Real.rpow_le_rpow (mul_nonneg (pow_nonneg hR.le _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (PDE.norm_le_vecEuclideanNorm ξ)
          (pow_nonneg hR.le _)) (by norm_num)
    have hb := (hdecay ξ).trans (mul_le_mul_of_nonneg_left hexp hC)
    simpa only [mul_assoc, mul_left_comm C] using
      mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg ξ) j)
  have h := integral_mono hi hi' hb
  rw [integral_const_mul, exitFrequencyMoment_scaling c j hR] at h
  exact h.trans_eq (by ring)

/-- A derivative of the actual inverse is controlled by the corresponding raw Fourier moment. -/
theorem ballExitL1Inversion_derivative_le_moment
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (j : ℕ) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    ‖iteratedFDeriv ℝ j (exitL1Inversion ν) y‖ ≤
      ((2 * Real.pi) ^ d)⁻¹ * (2 * Real.pi * ‖exitInversePairing d‖) ^ j *
        ∫ ξ, ‖ξ‖ ^ j * ‖exitL1Fourier ν ξ‖ := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let L := exitInversePairing d
  let F : PDE.Vec d → ContinuousMultilinearMap ℝ (fun _ : Fin j => PDE.Vec d)
      (Lp ℂ 1 (exitMarginal ν)) :=
    fun ξ => VectorFourier.fourierPowSMulRight L (exitL1Fourier ν) ξ j
  have hm (n : ℕ) (_hn : (n : ℕ∞) ≤ ⊤) :
      Integrable (fun ξ => ‖ξ‖ ^ n * ‖exitL1Fourier ν ξ‖) :=
    ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR P T hv hT n
  have hi : AEStronglyMeasurable (exitL1Fourier ν) volume :=
    (continuous_exitL1Fourier ν).aestronglyMeasurable
  have hmul := VectorFourier.integrable_fourierPowSMulRight L (hm j (by simp)) hi
  have hnon : 0 ≤ ((2 * Real.pi) ^ d)⁻¹ := by positivity
  rw [ballExitL1Inversion_iteratedFDeriv hH hLE hd hlam hLam B hB v₀ hR P T hv hT,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hnon]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hnon
  calc
    ‖VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ F y‖ ≤
        ∫ ξ, ‖F ξ‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi * ‖L‖) ^ j * (‖ξ‖ ^ j * ‖exitL1Fourier ν ξ‖) := by
      apply integral_mono_ae hmul.norm ((hm j (by simp)).const_mul _)
      apply Filter.Eventually.of_forall
      intro ξ
      convert! VectorFourier.norm_fourierPowSMulRight_le L (exitL1Fourier ν) ξ j using 1
      ring
    _ = _ := by rw [integral_const_mul]

/-- Structural constants precede coefficients and pole data in the raw derivative bound. -/
theorem ballExitL1Inversion_uniform_derivative_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C_m : ℕ → ℝ, (∀ j, 0 ≤ C_m j) ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time = R ^ 2 / 8 →
      ∀ (j : ℕ) (y : PDE.Vec d),
        ‖iteratedFDeriv ℝ j
          (exitL1Inversion (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)) y‖ ≤
          C_m j * R ^ (-3 * ((d : ℝ) + (j : ℝ))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    ballExit_fourier_decay hH hLE d hd lam Lam hlam hLam
  let A (j : ℕ) := ((2 * Real.pi) ^ d)⁻¹ *
    (2 * Real.pi * ‖exitInversePairing d‖) ^ j
  let D (j : ℕ) := A j * C * exitFrequencyMoment (d := d) c j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp only [A]; positivity
  refine ⟨D, fun j => mul_nonneg (mul_nonneg (hA j) hC.le)
    (exitFrequencyMoment_nonneg c j), ?_⟩
  intro B hB v₀ R hR P T hv hT j y
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hi := ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT j
  have hb := exitL1Fourier_moment_bound hd ν hC.le hc hR
    (hdecay B hB v₀ R hR P T hv hT) j hi
  have hdv := ballExitL1Inversion_derivative_le_moment hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT j y
  have hp : ((R ^ 3) ^ (d + j))⁻¹ = R ^ (-3 * ((d : ℝ) + (j : ℝ))) := by
    rw [neg_mul, Real.rpow_neg hR.le]
    congr 1
    rw [← Real.rpow_natCast R 3, ← Real.rpow_natCast _ (d + j),
      ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    ring
  refine hdv.trans ((mul_le_mul_of_nonneg_left hb (hA j)).trans_eq ?_)
  rw [hp]
  dsimp only [D, A]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
