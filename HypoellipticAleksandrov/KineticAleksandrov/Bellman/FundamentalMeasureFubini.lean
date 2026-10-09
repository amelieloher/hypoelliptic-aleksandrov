module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureEndpoint
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Absolute integrability and Fubini for compact tests away from the pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Punctured Lebesgue measure is sigma-finite on its locally compact carrier. -/
instance bellmanPuncturedVolume_sigmaFinite : SigmaFinite bellmanPuncturedVolume := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  infer_instance

/-- A compact test supported away from the origin remains compact on the punctured plane. -/
theorem bellman_test_compact_subtype {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    HasCompactSupport (fun q : BellmanPuncturedPlane => f q.val) := by
  have hK : IsCompact ((Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) ⁻¹' tsupport f) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hc
    intro q hq
    exact ⟨⟨q, hs hq⟩, rfl⟩
  exact hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage f continuous_subtype_val)

/-- Compactly supported continuous tests are integrable for the actual fundamental measure. -/
theorem bellman_integrable_fundamental_test {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    Integrable (fun q : BellmanPuncturedPlane => f q.val) bellmanFundamentalMeasure :=
  (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (bellman_test_compact_subtype hc hs)

/-- Absolute spacetime integrability of the Gaussian against a compact punctured test. -/
theorem bellman_integrable_gaussian_test {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    Integrable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      bellmanGaussianKernel w.1 w.2.val * f w.2.val)
      (bellmanPositiveTimeVolume.prod bellmanPuncturedVolume) := by
  have hcp := bellman_test_compact_subtype hc hs
  obtain ⟨a, ha, hb⟩ := bellmanPunctured_compact_lower_bound _ hcp
  have hfi : Integrable (fun q : BellmanPuncturedPlane => |f q.val|)
      bellmanPuncturedVolume :=
    ((hf.comp continuous_subtype_val).integrable_of_hasCompactSupport hcp).abs
  have hm : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      bellmanGaussianKernel w.1 w.2.val * f w.2.val) := by
    apply Continuous.measurable
    exact (continuous_bellmanGaussianKernel.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mul
      (hf.comp (continuous_subtype_val.comp continuous_snd))
  refine ((integrable_bellmanTimeMajorant a).mul_prod hfi).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (bellmanGaussianKernel_pos w.1 w.2.val)]
  by_cases hq : w.2 ∈ tsupport (fun q : BellmanPuncturedPlane => f q.val)
  · exact mul_le_mul_of_nonneg_right
      (bellmanGaussianKernel_le_timeMajorant a ha w.2.val (hb _ hq) w.1) (abs_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hq]

/-- Absolute spacetime integrability of the Gaussian time derivative against a compact test. -/
theorem bellman_integrable_gaussian_timeDerivative_test {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    Integrable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      (bellmanGaussianTimeCoefficient w.1.val w.2.val *
        bellmanGaussianKernel w.1 w.2.val) * f w.2.val)
      (bellmanPositiveTimeVolume.prod bellmanPuncturedVolume) := by
  have hcp := bellman_test_compact_subtype hc hs
  obtain ⟨a, ha, hb⟩ := bellmanPunctured_compact_lower_bound _ hcp
  have hweight : Continuous bellmanGaussianTimeWeight := by
    unfold bellmanGaussianTimeWeight
    fun_prop
  have hfi : Integrable (fun q : BellmanPuncturedPlane =>
      bellmanGaussianTimeWeight q.val * |f q.val|) bellmanPuncturedVolume :=
    ((hweight.comp continuous_subtype_val).mul (hf.comp continuous_subtype_val).abs)
      |>.integrable_of_hasCompactSupport hcp.abs.mul_left
  have hm : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      (bellmanGaussianTimeCoefficient w.1.val w.2.val *
        bellmanGaussianKernel w.1 w.2.val) * f w.2.val) := by
    have hg : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
        bellmanGaussianKernel w.1 w.2.val) := (continuous_bellmanGaussianKernel.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).measurable
    apply Measurable.mul (Measurable.mul ?_ hg)
      (hf.measurable.comp (measurable_subtype_coe.comp measurable_snd))
    unfold bellmanGaussianTimeCoefficient
    fun_prop
  refine ((integrable_bellmanDerivativeMajorant a).mul_prod hfi).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul, Real.norm_eq_abs (f w.2.val)]
  by_cases hq : w.2 ∈ tsupport (fun q : BellmanPuncturedPlane => f q.val)
  · have h := mul_le_mul_of_nonneg_right
      (bellmanGaussianTimeDerivative_le_majorant a ha w.2.val (hb _ hq) w.1)
      (abs_nonneg (f w.2.val))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  · simp [image_eq_zero_of_notMem_tsupport hq]

/-- The literal density's real value is the Bochner integral of the positive kernel. -/
theorem bellmanFundamentalDensity_toReal (q : BellmanPuncturedPlane) :
    (bellmanFundamentalDensity q).toReal =
      ∫ t, bellmanGaussianKernel t q.val ∂bellmanPositiveTimeVolume := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun t => (bellmanGaussianKernel_pos t q.val).le)
    (integrable_bellmanGaussianKernel_time q).aestronglyMeasurable).symm

/-- Fundamental-measure integration is the time integral of the literal Gaussian pairing. -/
theorem bellmanFundamentalMeasure_integral_test {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    (∫ q : BellmanPuncturedPlane, f q.val ∂bellmanFundamentalMeasure) =
      ∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q * f q)
        ∂bellmanPositiveTimeVolume := by
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  rw [bellmanFundamentalMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_bellmanFundamentalDensity
    (ae_of_all _ fun q => (bellmanFundamentalDensity_ne_top q).lt_top)]
  simp only [smul_eq_mul, bellmanFundamentalDensity_toReal, ← integral_mul_const]
  rw [integral_integral_swap
    (f := fun q : BellmanPuncturedPlane => fun t : BellmanPositiveTime =>
      bellmanGaussianKernel t q.val * f q.val)
    (bellman_integrable_gaussian_test hf hc hs).swap]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [← map_bellmanPuncturedVolume_coe, he.integral_map]

/-- The Gaussian time derivative has zero total spacetime pairing with a punctured test. -/
theorem bellmanGaussianTimeDerivative_integral_test_eq_zero {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ,
      (bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q) * f q)
        ∂bellmanPositiveTimeVolume) = 0 := by
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  have heq (t : BellmanPositiveTime) :
      (∫ q : ℝ × ℝ, (bellmanGaussianTimeCoefficient t.val q *
        bellmanGaussianKernel t q) * f q) =
      ∫ q : BellmanPuncturedPlane, (bellmanGaussianTimeCoefficient t.val q.val *
        bellmanGaussianKernel t q.val) * f q.val ∂bellmanPuncturedVolume := by
    rw [← map_bellmanPuncturedVolume_coe, he.integral_map]
  simp_rw [heq]
  rw [integral_integral_swap (bellman_integrable_gaussian_timeDerivative_test hf hc hs)]
  simp only [integral_mul_const, integral_bellmanGaussianTimeDerivative_eq_zero,
    zero_mul, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov
