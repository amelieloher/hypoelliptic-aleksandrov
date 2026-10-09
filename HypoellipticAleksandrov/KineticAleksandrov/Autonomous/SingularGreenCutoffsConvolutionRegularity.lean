module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionBounds

/-! # Measurability and regularity of the literal position-convolution jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- Both scalar kernel derivatives used in the second parameter jet are continuous. -/
theorem barrier_kernel_derivatives_continuous (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) :
    Continuous (deriv κ) ∧ Continuous (deriv (deriv κ)) := by
  have hd : ContDiff ℝ 1 (deriv κ) := hκ.deriv'
  exact ⟨hκ.continuous_deriv (by norm_num), hd.continuous_deriv_one⟩

/-- Actual punctured Bellman jets are Borel functions on the full plane. -/
theorem barrier_velocity_jets_measurable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) :
    Measurable (bellmanDv phi) ∧ Measurable (bellmanDvv phi) :=
  ⟨measurable_of_continuousOn_compl_singleton (0, 0)
      (h.directional_contDiffOn (0, 1)).continuousOn,
    measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn⟩

/-- For fixed nonzero position the velocity jet functions are continuous in every parameter. -/
theorem barrier_velocity_jets_parameter_continuous {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (Y : ℝ) (hY : Y ≠ 0) :
    Continuous (fun q : ℝ × ℝ => bellmanDv phi (Y, q.2)) ∧
      Continuous (fun q : ℝ × ℝ => bellmanDvv phi (Y, q.2)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (Y, q.2)) univ bellmanPuncturedSet :=
    fun _ _ he => hY (congrArg Prod.fst he)
  have hc : ContinuousOn (fun q : ℝ × ℝ => (Y, q.2)) univ :=
    (continuous_const.prodMk continuous_snd).continuousOn
  exact ⟨continuousOn_univ.mp ((h.directional_contDiffOn (0, 1)).continuousOn.comp hc hmap),
    continuousOn_univ.mp (h.dvv_continuousOn.comp hc hmap)⟩

/-- Scalar measurable coefficients give a measurable coordinate linear form. -/
theorem barrier_projection_measurable {T : Type*} [MeasurableSpace T]
    {a b : T → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => a x • barrierPositionProjection + b x • barrierVelocityProjection) :=
  (ha.smul measurable_const).add (hb.smul measurable_const)

/-- Scalar continuous coefficients give a continuous coordinate linear form. -/
theorem barrier_projection_continuous {T : Type*} [TopologicalSpace T]
    {a b : T → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => a x • barrierPositionProjection + b x • barrierVelocityProjection) :=
  (ha.smul continuous_const).add (hb.smul continuous_const)

/-- Both convolution parameter jets are measurable in the position integration variable. -/
theorem barrierConvolutionJets_measurable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (q : ℝ × ℝ) :
    Measurable (barrierConvolutionJet κ phi q) ∧
      Measurable (barrierConvolutionSecondJet κ phi q) := by
  obtain ⟨hk1, hk2⟩ := barrier_kernel_derivatives_continuous κ hκ
  obtain ⟨hmv, hmvv⟩ := barrier_velocity_jets_measurable h
  have hm0 : Measurable (fun Y : ℝ => bellmanOriginExtension phi (Y, q.2)) :=
    (h.origin_extension_continuous ha).measurable.comp
    (measurable_id.prodMk measurable_const)
  have hm1 : Measurable (fun Y : ℝ => bellmanDv phi (Y, q.2)) := hmv.comp (measurable_id.prodMk
    measurable_const)
  have hm2 : Measurable (fun Y : ℝ => bellmanDvv phi (Y, q.2)) := hmvv.comp (measurable_id.prodMk
    measurable_const)
  have hk0 : Measurable (fun Y : ℝ => κ (q.1 - Y)) := hκ.continuous.measurable.comp
    (measurable_const.sub measurable_id)
  have hk1' : Measurable (fun Y : ℝ => deriv κ (q.1 - Y)) := hk1.measurable.comp
    (measurable_const.sub measurable_id)
  have hk2' : Measurable (fun Y : ℝ => deriv (deriv κ) (q.1 - Y)) := hk2.measurable.comp
    (measurable_const.sub measurable_id)
  constructor
  · exact barrier_projection_measurable (hk1'.mul hm0) (hk0.mul hm1)
  · let LX := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
      barrierPositionProjection
    let Lv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
      barrierVelocityProjection
    have h1 := barrier_projection_measurable (hk2'.mul hm0) (hk1'.mul hm1)
    have h2 := barrier_projection_measurable (hk1'.mul hm1) (hk0.mul hm2)
    exact (LX.continuous.measurable.comp h1).add (Lv.continuous.measurable.comp h2)

/-- The second convolution parameter jet is continuous off the null integration position. -/
theorem barrierConvolutionSecondJet_continuous {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (Y : ℝ) (hY : Y ≠ 0) :
    Continuous (fun q => barrierConvolutionSecondJet κ phi q Y) := by
  obtain ⟨hk1, hk2⟩ := barrier_kernel_derivatives_continuous κ hκ
  obtain ⟨hv, hvv⟩ := barrier_velocity_jets_parameter_continuous h Y hY
  have hp : Continuous (fun q : ℝ × ℝ => bellmanOriginExtension phi (Y, q.2)) :=
    (h.origin_extension_continuous ha).comp (continuous_const.prodMk continuous_snd)
  have hk0 : Continuous (fun q : ℝ × ℝ => κ (q.1 - Y)) := hκ.continuous.comp (continuous_fst.sub
    continuous_const)
  have hk1' : Continuous (fun q : ℝ × ℝ => deriv κ (q.1 - Y)) := hk1.comp (continuous_fst.sub
    continuous_const)
  have hk2' : Continuous (fun q : ℝ × ℝ => deriv (deriv κ) (q.1 - Y)) := hk2.comp
    (continuous_fst.sub continuous_const)
  let LX := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
    barrierPositionProjection
  let Lv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
    barrierVelocityProjection
  have h1 := barrier_projection_continuous (hk2'.mul hp) (hk1'.mul hv)
  have h2 := barrier_projection_continuous (hk1'.mul hv) (hk0.mul hvv)
  exact (LX.continuous.comp h1).add (Lv.continuous.comp h2)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
