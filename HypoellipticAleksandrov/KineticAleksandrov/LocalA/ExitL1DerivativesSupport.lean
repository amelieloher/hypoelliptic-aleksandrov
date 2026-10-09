module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1InversionReal
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupport
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Compact position support and its raw volume for the single real inverse -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo
open scoped ENNReal

/-- The Euclidean cone is contained in a compact coordinate ball of radius `R³`. -/
theorem ballExit_ae_position_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ∀ᵐ p ∂ballExit hH hLE hd hlam hLam B hB v₀ hR P T, ‖p.1‖ ≤ R ^ 3 := by
  filter_upwards [ballExit_cone hH hLE hd hlam hLam B hB v₀ hR P T] with p hp
  have ht : p.2.1 - P.1.time ≤ R ^ 2 / 8 := by linarith only [hp.2.1, hT]
  have hcone := (PDE.norm_le_vecEuclideanNorm p.1).trans hp.2.2
  have hs := mul_le_mul_of_nonneg_left ht hR.le
  have hpow : R * (R ^ 2 / 8) ≤ R ^ 3 := by
    have hnn := pow_nonneg hR.le 3
    nlinarith
  exact hcone.trans (hs.trans hpow)

/-- The smooth real inverse vanishes everywhere outside the compact reached-position ball. -/
theorem ballExitL1Density_zero_outside
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ∀ y : PDE.Vec d, R ^ 3 < ‖y‖ →
      exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) y = 0 := by
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let G := exitL1Density ν
  let U : Set (PDE.Vec d) := {y | R ^ 3 < ‖y‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hm := measurable_exitJointDensity ν
  have hs := ballExit_ae_position_bound hH hLE hd hlam hLam B hB v₀ hR P T hT
  rw [ballExit_eq_withDensity_exitJointDensity hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT, ae_withDensity_iff hm.ennreal_ofReal] at hs
  have hs' := Measure.ae_ae_of_ae_prod hs
  have hnon := ballExitPositionKernel_density hH hLE hd hlam hLam B hB v₀ hR P T hv hT
  have hzero : ∀ᵐ y ∂(volume : Measure (PDE.Vec d)), y ∈ U → G y = 0 := by
    filter_upwards [hs'] with y hy
    intro hyU
    apply Lp.ext
    filter_upwards [ballExitL1Density_coe hH hLE hd hlam hLam B hB v₀ hR P T hv hT y,
      hy, hnon, Lp.coeFn_zero (E := ℂ) (p := 1) (μ := exitMarginal ν)]
      with z hz hzs hzn hz0
    have hg : exitJointDensity ν (y, z) = 0 := by
      have hge := hzn.2 y
      have hle : exitJointDensity ν (y, z) ≤ 0 := by
        apply ENNReal.ofReal_eq_zero.mp
        by_contra hne
        exact (not_le_of_gt hyU) (hzs hne)
      exact le_antisymm hle hge
    rw [hz, hg, Complex.ofReal_zero, hz0]
    rfl
  have hae : G =ᵐ[volume.restrict U] (fun _ => 0) :=
    (ae_restrict_iff' hU.measurableSet).mpr hzero
  have hcont := (ballExitL1Density_contDiff hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT).continuous
  exact fun y hy => Measure.eqOn_open_of_ae_eq hae hU hcont.continuousOn continuousOn_const hy

/-- The support bounding ball has the required raw `R^(3d)` volume. -/
theorem exitPositionBoundingBall_volume {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (volume : Measure (PDE.Vec d)) (Metric.closedBall 0 (R ^ 3)) =
      ENNReal.ofReal ((2 : ℝ) ^ d * R ^ (3 * d)) := by
  rw [Real.volume_pi_closedBall _ (pow_pos hR 3).le, Fintype.card_fin,
    mul_pow, ← pow_mul]

/-- Every derivative of a compactly supported position function has the same support bound. -/
theorem exitDerivative_zero_outside {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : PDE.Vec d → E) (r : ℝ)
    (hzero : ∀ y, r < ‖y‖ → G y = 0) (j : ℕ) :
    ∀ y, r < ‖y‖ → iteratedFDeriv ℝ j G y = 0 := by
  have hs : Function.support G ⊆ Metric.closedBall 0 r := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hzero y (lt_of_not_ge h))
  have hts : tsupport G ⊆ Metric.closedBall 0 r :=
    closure_minimal hs Metric.isClosed_closedBall
  intro y hy
  apply Function.notMem_support.mp
  intro hmem
  have hm := hts (support_iteratedFDeriv_subset j hmem)
  rw [Metric.mem_closedBall, dist_zero_right] at hm
  exact (not_le_of_gt hy) hm

/-- Raw support volume bounds the integral of any globally bounded derivative. -/
theorem exitDerivative_integral_le_volume {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : PDE.Vec d → E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ y, R ^ 3 < ‖y‖ → G y = 0) (j : ℕ) {M : ℝ}
    (_hM : 0 ≤ M) (hbound : ∀ y, ‖iteratedFDeriv ℝ j G y‖ ≤ M) :
    (∫ y, ‖iteratedFDeriv ℝ j G y‖) ≤ ((2 : ℝ) ^ d * R ^ (3 * d)) * M := by
  have hz := exitDerivative_zero_outside G (R ^ 3) hzero j
  have he : (∫ y in Metric.closedBall 0 (R ^ 3), ‖iteratedFDeriv ℝ j G y‖) =
      ∫ y, ‖iteratedFDeriv ℝ j G y‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      rw [hz y hy, norm_zero])
  have hf : (volume : Measure (PDE.Vec d)) (Metric.closedBall 0 (R ^ 3)) < ⊤ :=
    (isCompact_closedBall (0 : PDE.Vec d) (R ^ 3)).measure_lt_top
  have hv := exitPositionBoundingBall_volume (d := d) hR
  have hb := norm_setIntegral_le_of_norm_le_const
    (f := fun y => ‖iteratedFDeriv ℝ j G y‖) hf (fun y _hy =>
    by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound y)
  have hvr : (volume : Measure (PDE.Vec d)).real (Metric.closedBall 0 (R ^ 3)) =
      (2 : ℝ) ^ d * R ^ (3 * d) := by
    rw [Measure.real, hv, ENNReal.toReal_ofReal (by positivity)]
  rw [he, hvr, Real.norm_eq_abs] at hb
  exact ((le_abs_self _).trans hb).trans_eq (mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
