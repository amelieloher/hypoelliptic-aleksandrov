module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1Inversion
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDisintegrationInversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import all Mathlib.Basic.Complex.Basic

/-! # Testing the inverse Fourier function against measurable exit-data sets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Reconstruction
open scoped ENNReal

/-- Integrating an `L¹` element over any measurable exit-data set is a continuous linear map. -/
def exitL1SetIntegral {d : ℕ} (m : Measure (TimeVelocity d)) (E : Set (TimeVelocity d)) :
    Lp ℂ 1 m →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (LpToLpRestrictCLM (TimeVelocity d) ℂ ℂ m 1 E)

/-- The continuous linear testing map is the literal set integral of a representative. -/
theorem exitL1SetIntegral_apply {d : ℕ} (m : Measure (TimeVelocity d))
    (E : Set (TimeVelocity d)) (f : Lp ℂ 1 m) :
    exitL1SetIntegral m E f = ∫ z in E, f z ∂m := by
  unfold exitL1SetIntegral
  rw [ContinuousLinearMap.comp_apply]
  rw [← L1.integral_eq' ℂ]
  rw [L1.integral_eq_integral]
  apply integral_congr_ae
  exact LpToLpRestrictCLM_coeFn ℂ E f

/-- The Fourier normalization pairing produces the physical positive inverse phase. -/
theorem exitInversePairing_phase {d : ℕ} (ξ y : PDE.Vec d) :
    (Real.fourierChar (-(exitInversePairing d ξ y)) : ℂ) =
      Complex.exp (Complex.I * (PDE.vecDot ξ y : ℂ)) := by
  rw [Real.fourierChar_apply]
  simp only [exitInversePairing, smul_apply, smul_eq_mul, exitDot_apply]
  congr 1
  push_cast
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  field_simp

/-- The inverse in the complete space has the literal physical Fourier-integral formula. -/
theorem exitL1Inversion_eq_integral {d : ℕ}
    (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν] (y : PDE.Vec d) :
    exitL1Inversion ν y = ((2 * Real.pi) ^ d)⁻¹ •
      ∫ ξ, Complex.exp (Complex.I * (PDE.vecDot ξ y : ℂ)) • exitL1Fourier ν ξ := by
  unfold exitL1Inversion VectorFourier.fourierIntegral
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    rw [Circle.smul_def]
    exact congrArg (fun c : ℂ => c • exitL1Fourier ν ξ) (exitInversePairing_phase ξ y))

/-- Multiplication by an inverse phase preserves joint integrability. -/
theorem ballExitInverseIntegrand_integrable
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    Integrable (fun p : PDE.Vec d × TimeVelocity d =>
      Complex.exp (Complex.I * (PDE.vecDot p.1 y : ℂ)) * exitFourierRep ν p.1 p.2)
      (volume.prod (exitMarginal ν)) := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hc : Continuous (fun ξ : PDE.Vec d =>
      Complex.exp (Complex.I * (PDE.vecDot ξ y : ℂ))) := by
    unfold PDE.vecDot
    fun_prop
  have hi := ballExitFourierRep_integrable_prod hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT
  change Integrable (fun p : PDE.Vec d × TimeVelocity d => exitFourierRep ν p.1 p.2)
    (volume.prod (exitMarginal ν)) at hi
  apply hi.norm.mono'
    ((hc.measurable.comp measurable_fst).mul
      (measurable_exitFourierRep ν)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_apply, Pi.mul_apply]
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The complete-space inverse agrees with the joint inverse representative on every test set. -/
theorem ballExitL1Inversion_setIntegral
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (y : PDE.Vec d)
    (E : Set (TimeVelocity d)) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    (∫ z in E, (exitL1Inversion ν y : TimeVelocity d → ℂ) z ∂exitMarginal ν) =
      ((2 * Real.pi) ^ d)⁻¹ •
        ∫ z in E, vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y ∂exitMarginal ν := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let phase (ξ : PDE.Vec d) := Complex.exp (Complex.I * (PDE.vecDot ξ y : ℂ))
  have hp : Continuous phase := by unfold phase PDE.vecDot; fun_prop
  have hpn (ξ : PDE.Vec d) : ‖phase ξ‖ = 1 := by
    unfold phase
    rw [Complex.norm_exp]
    simp
  have hF : Integrable (exitL1Fourier ν) :=
    (integrable_norm_iff (continuous_exitL1Fourier ν).aestronglyMeasurable).mp (by
      simpa only [pow_zero, one_mul] using
        ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR P T hv hT 0)
  have hFi : Integrable (fun ξ => phase ξ • exitL1Fourier ν ξ) := by
    apply hF.norm.mono' (hp.smul (continuous_exitL1Fourier ν)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      change ‖phase ξ • exitL1Fourier ν ξ‖ ≤ ‖exitL1Fourier ν ξ‖
      rw [norm_smul, hpn, one_mul])
  have hi := ballExitInverseIntegrand_integrable hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT y
  have hir : Integrable (fun p : PDE.Vec d × TimeVelocity d =>
      phase p.1 * exitFourierRep ν p.1 p.2)
      (volume.prod ((exitMarginal ν).restrict E)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← exitL1SetIntegral_apply, exitL1Inversion_eq_integral]
  rw [(exitL1SetIntegral (exitMarginal ν) E).map_smul_of_tower,
    ← (exitL1SetIntegral (exitMarginal ν) E).integral_comp_comm hFi]
  congr 1
  calc
    (∫ ξ, exitL1SetIntegral (exitMarginal ν) E (phase ξ • exitL1Fourier ν ξ)) =
        ∫ ξ, phase ξ * ∫ z in E, exitFourierRep ν ξ z ∂exitMarginal ν := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ
      dsimp only
      rw [map_smul, exitL1SetIntegral_apply, smul_eq_mul]
      congr 1
      exact integral_congr_ae (ae_restrict_of_ae (coe_exitL1Fourier ν ξ))
    _ = ∫ z in E, vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y
        ∂exitMarginal ν := by
      simp_rw [← integral_const_mul]
      exact integral_integral_swap hir

/-- The complete-space inverse has the explicit inverse-integral representative at every y. -/
theorem ballExitL1Inversion_coe
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    (exitL1Inversion ν y : TimeVelocity d → ℂ) =ᵐ[exitMarginal ν]
      fun z => ((2 * Real.pi) ^ d)⁻¹ •
        vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hi := ballExitInverseIntegrand_integrable hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT y
  have hir : Integrable (fun z => ((2 * Real.pi) ^ d)⁻¹ •
      vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y) (exitMarginal ν) :=
    by
      convert! hi.integral_prod_right.smul (((2 * Real.pi) ^ d)⁻¹ : ℝ) using 1
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) hir
  intro E _hE _hfin
  rw [integral_smul]
  exact ballExitL1Inversion_setIntegral hH hLE hd hlam hLam B hB v₀ hR P T hv hT y E

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
