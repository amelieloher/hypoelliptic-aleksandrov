module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionWindow

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Actual C² regularity of position smoothing, including zero velocity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Position smoothing is C² on the entire physical plane, without a regularity premise. -/
theorem positionBarrierConvolution_jet_spec {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) :
    ∀ q0 : ℝ × ℝ,
      ContDiffAt ℝ 2 (positionBarrierConvolution κ phi) q0 ∧
      HasFDerivAt (positionBarrierConvolution κ phi) (∫ Y, barrierConvolutionJet κ phi q0 Y) q0 ∧
      HasFDerivAt (fun q => ∫ Y, barrierConvolutionJet κ phi q Y)
        (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) q0 := by
  intro q0
  obtain ⟨R, hR, hwindow⟩ := barrier_convolution_support_window κ hs q0
  let K := Icc (-R) R
  let U := Metric.ball q0 1
  let mu := volume.restrict K
  have hmu : IsFiniteMeasure mu := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  let := hmu
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hbκ0, hbκ1, hbκ2⟩ :=
    barrier_kernel_uniform_bounds κ hκ hs
  obtain ⟨_, _, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  have hψ := h.origin_extension_continuous ha
  obtain ⟨B0, hB0b⟩ := ((isCompact_Icc (a := -R) (b := R)).prod
    (isCompact_Icc (a := q0.2 - 1) (b := q0.2 + 1))).exists_bound_of_continuousOn
      hψ.continuousOn
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbphi (q : ℝ × ℝ) (hq : q ∈ U) (Y : ℝ) (hY : Y ∈ K) :
      |bellmanOriginExtension phi (Y, q.2)| ≤ B := by
    have hqv := (barrier_parameter_ball_bounds hq).2
    have hv : q.2 ∈ Icc (q0.2 - 1) (q0.2 + 1) := by
      have hh := abs_lt.mp hqv
      constructor <;> linarith only [hh.1, hh.2]
    have hh := hB0b (Y, q.2) ⟨hY, hv⟩
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (le_max_left _ _)
  let p1 := (alpha - 1) / 3
  let p2 := (alpha - 2) / 3
  let b0 := fun _ : ℝ => K0 * B
  let b1 := fun Y : ℝ => K1 * B + K0 * Cv * |Y| ^ p1
  let b2 := fun Y : ℝ => K2 * B + 2 * K1 * Cv * |Y| ^ p1 + K0 * Cvv * |Y| ^ p2
  have hi1 : Integrable (fun Y : ℝ => |Y| ^ p1) mu :=
    (bellman_abs_rpow_locallyIntegrable p1 (by dsimp only [p1]; linarith))
      |>.integrableOn_isCompact isCompact_Icc
  have hi2 : Integrable (fun Y : ℝ => |Y| ^ p2) mu :=
    (bellman_abs_rpow_locallyIntegrable p2 (by dsimp only [p2]; linarith))
      |>.integrableOn_isCompact isCompact_Icc
  have hb0 : Integrable b0 mu := integrable_const _
  have hb1 : Integrable b1 mu := (integrable_const _).add (hi1.const_mul (K0 * Cv))
  have hb2 : Integrable b2 mu := ((integrable_const _).add
    (hi1.const_mul (2 * K1 * Cv))).add (hi2.const_mul (K0 * Cvv))
  let : TopologicalSpace.PseudoMetrizableSpace
      ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := by
    let m : PseudoMetricSpace ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := inferInstance
    exact ⟨⟨m.toUniformSpace, rfl, inferInstance⟩⟩
  have hmeas0 (q : ℝ × ℝ) : Measurable (barrierConvolutionIntegrand κ phi q) :=
    (hκ.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
      (hψ.measurable.comp (measurable_id.prodMk measurable_const))
  have hmeas1 q := (barrierConvolutionJets_measurable h ha κ hκ q).1
  have hmeas2 q := (barrierConvolutionJets_measurable h ha κ hκ q).2
  have hae : ∀ᵐ Y ∂mu, Y ∈ K ∧ Y ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY hn
    exact ⟨hY, hn⟩
  have hs2 : ContDiffOn ℝ 2 (fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu) U ∧
      (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionIntegrand κ phi p Y ∂mu)
        (∫ Y, barrierConvolutionJet κ phi q Y ∂mu) q) ∧
      (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionJet κ phi p Y ∂mu)
        (∫ Y, barrierConvolutionSecondJet κ phi q Y ∂mu) q) := by
    apply singular_parameter_integral_contDiffOn_two mu Metric.isOpen_ball
      (barrierConvolutionIntegrand κ phi) (barrierConvolutionJet κ phi)
      (barrierConvolutionSecondJet κ phi) b0 b1 b2 hb0 hb1 hb2
      (fun q _ => (hmeas0 q).aestronglyMeasurable)
      (fun q _ => (hmeas1 q).aestronglyMeasurable)
      (fun q _ => (hmeas2 q).aestronglyMeasurable)
    · filter_upwards [hae] with Y hY
      intro q hq
      rw [barrierConvolutionIntegrand, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbκ0 _) (hbphi q hq Y hY.1) (abs_nonneg _) hK0
    · filter_upwards [hae] with Y hY
      intro q hq
      have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
        Y q.2 hY.2
      apply (barrierConvolutionJet_norm_le κ phi q Y).trans
      dsimp only [b1, p1]
      calc
        _ ≤ K1 * B + K0 * (Cv * |Y| ^ ((alpha - 1) / 3)) := by
          gcongr
          all_goals first
          | exact hbκ1 _
          | exact hbphi q hq Y hY.1
          | exact hbκ0 _
        _ = _ := by ring
    · filter_upwards [hae] with Y hY
      intro q hq
      have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
        Y q.2 hY.2
      have hvvb := barrier_position_fiber_bound (alpha - 2) (by linarith) _ Cvv hCvv hbvv
        Y q.2 hY.2
      apply (barrierConvolutionSecondJet_norm_le κ phi q Y).trans
      dsimp only [b2, p1, p2]
      calc
        _ ≤ K2 * B + 2 * K1 * (Cv * |Y| ^ ((alpha - 1) / 3)) +
            K0 * (Cvv * |Y| ^ ((alpha - 2) / 3)) := by
          gcongr
          all_goals first
          | exact hbκ2 _
          | exact hbphi q hq Y hY.1
          | exact hbκ1 _
          | exact hvb
          | exact hbκ0 _
        _ = _ := by ring
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      intro q _
      exact barrierConvolutionIntegrand_hasFDerivAt h κ hκ q Y hY
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      intro q _
      exact barrierConvolutionJet_hasFDerivAt h κ hκ q Y hY
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      exact (barrierConvolutionSecondJet_continuous h ha κ hκ Y hY).continuousOn
  have he : positionBarrierConvolution κ phi =ᶠ[𝓝 q0]
      fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu := by
    filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    rw [barrierConvolutionIntegrand, (hwindow q hq Y hY).1, zero_mul]
  have hq0 : q0 ∈ U := Metric.mem_ball_self (by norm_num)
  have he1 : (fun q => ∫ Y, barrierConvolutionJet κ phi q Y) =ᶠ[𝓝 q0]
      fun q => ∫ Y, barrierConvolutionJet κ phi q Y ∂mu := by
    filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    obtain ⟨h0, h1, _⟩ := hwindow q hq Y hY
    simp only [barrierConvolutionJet, h0, h1, zero_mul, zero_smul, add_zero]
  have he2 : (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) =
      ∫ Y, barrierConvolutionSecondJet κ phi q0 Y ∂mu := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    obtain ⟨h0, h1, h2⟩ := hwindow q0 hq0 Y hY
    simp only [barrierConvolutionSecondJet, h0, h1, h2, zero_mul, zero_smul, add_zero,
      ContinuousLinearMap.zero_smulRight]
    apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro u
    simp only [add_apply, zero_apply, zero_add]
  have hcd := (hs2.1 q0 hq0).contDiffAt (Metric.ball_mem_nhds q0 (by norm_num))
  refine ⟨hcd.congr_of_eventuallyEq he, ?_, ?_⟩
  · rw [he1.eq_of_nhds]
    exact (hs2.2.1 q0 hq0).congr_of_eventuallyEq he
  · rw [he2]
    exact (hs2.2.2 q0 hq0).congr_of_eventuallyEq he1

/-- Position smoothing is C² on the entire physical plane, including zero velocity. -/
theorem positionBarrierConvolution_contDiff {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) :
    ContDiff ℝ 2 (positionBarrierConvolution κ phi) := by
  rw [contDiff_iff_contDiffAt]
  exact fun q => (positionBarrierConvolution_jet_spec h ha ha1 κ hκ hs q).1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
