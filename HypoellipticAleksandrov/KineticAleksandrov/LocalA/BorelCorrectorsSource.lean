module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsCutoff
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Vanishing compact residual norms for Borel homogeneous solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Filter
open scoped Topology ENNReal Matrix.Norms.Elementwise

/-- The cutoff residual vanishes in each finite Lp norm under coefficient mollification. -/
theorem borelCorrectorSource_norm_tendsto {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (B : ℕ → CoefficientField d)
    (hB : ∀ j, IsSmoothCoefficient (B j) ∧ IsSymmetricCoefficient (B j) ∧
      HasLowerEllipticity lam (B j) ∧ HasUpperEllipticity Lam (B j))
    (hconv : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (B j) z) atTop (𝓝 (coefficientAt A z)))
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (U : KineticPoint d → ℝ) (hu : IsKineticC112On U D)
    (he : ∀ᵐ P ∂volume.restrict D,
      forwardKineticOperator (ofTimeVelocityCoefficient A) U P = 0)
    (χ : KineticPoint d → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ D) (hχb : ∀ P, 0 ≤ χ P ∧ χ P ≤ 1)
    {p : ℝ} (hp : 0 < p) :
    (∀ j, MemLp (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume) ∧
    Tendsto (fun j => (eLpNorm (borelCorrectorSource χ (B j) U)
      (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
  let K := tsupport χ
  have hK : IsCompact K := hχc
  have hhm : ContinuousOn (kineticVelocityHessian U) K :=
    hu.continuousOn_kineticVelocityHessian.mono hs
  obtain ⟨_, hErr, hErr0⟩ := borel_inner_error hlam hLam A hA hlo hhi
    B hB hconv K hK (kineticVelocityHessian U) hhm hp
  have hEq j : K.indicator (borelCorrectorSource χ (B j) U) =
      borelCorrectorSource χ (B j) U := by
    apply indicator_eq_self.mpr
    intro P hP
    exact subset_tsupport χ (by
      intro hz
      apply hP
      simp only [borelCorrectorSource, hz, zero_mul])
  have hnorm j : eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume =
      eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) (volume.restrict K) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet, hEq j]
  have hb j : ∀ᵐ P ∂volume.restrict K,
      ‖borelCorrectorSource χ (B j) U P‖ ≤ ‖borelCoefficientError (B j) A
        (kineticVelocityHessian U) P‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs he] with P hP
    have hop := borelCorrector_operator_sub (B j) A U P
    rw [hP, sub_zero] at hop
    simp only [borelCorrectorSource, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hχb P).1, hop, borelCoefficientError, abs_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχb P).2
  have hmem j : MemLp (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p)
      (volume.restrict K) := by
    have hc := (borelCorrectorSource_continuous_compact hD χ hχ hχc hs
      (B j) (hB j).1 U hu).1
    exact (hErr j).of_le hc.measurable.aestronglyMeasurable.restrict (hb j)
  have hbound j : (eLpNorm (borelCorrectorSource χ (B j) U)
      (ENNReal.ofReal p) volume).toReal ≤
      (eLpNorm (borelCoefficientError (B j) A (kineticVelocityHessian U))
        (ENNReal.ofReal p) (volume.restrict K)).toReal := by
    rw [hnorm j]
    exact ENNReal.toReal_mono (hErr j).eLpNorm_ne_top
      (eLpNorm_mono_ae (hmem j).aestronglyMeasurable (hb j))
  refine ⟨fun j => ?_, ?_⟩
  · have hm := (memLp_indicator_iff_restrict hK.measurableSet).mpr (hmem j)
    rwa [hEq j] at hm
  · exact squeeze_zero (fun j => ENNReal.toReal_nonneg) hbound hErr0

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
