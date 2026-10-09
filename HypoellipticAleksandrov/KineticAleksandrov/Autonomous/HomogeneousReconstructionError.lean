module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal

/-! # Actual Green estimates for the three source localization errors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology ENNReal

/-- Every Green source time is strictly later than its pole time. -/
theorem reconstruction_green_ae_time_gt (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    ∀ᵐ p ∂stripGreenOfKernel H K T e, e.1.time < p.time := by
  unfold stripGreenOfKernel
  apply (ae_map_iff (measurable_elapsedPhysicalPoint _ _).aemeasurable
    (measurableSet_lt measurable_const continuous_time.measurable)).2
  exact Eventually.of_forall fun q => by
    change e.1.time < e.1.time + q.1.1
    exact lt_add_of_pos_right _ q.1.2.1

/-- The proper spatial weight is integrable against the actual finite Green measure. -/
theorem reconstruction_green_spatial_integrable
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    Integrable (fun p => reconstructionSpatialWeight (p.position 0))
      (stripGreenOfKernel H E.2 T e) := by
  have hm : Continuous (fun p : Point => reconstructionSpatialWeight (p.position 0)) :=
    reconstructionSpatialWeight_smooth.continuous.comp
      ((continuous_apply 0).comp continuous_position)
  refine ⟨hm.measurable.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).mpr ?_⟩
  exact lt_of_le_of_lt
    (reconstruction_green_spatial_weight_bound hH hlam hLam A H E hE T e)
    ENNReal.ofReal_lt_top

/-- The spatial moment bound also holds for the ordinary integral. -/
theorem reconstruction_green_spatial_integral_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∫ p, reconstructionSpatialWeight (p.position 0) ∂stripGreenOfKernel H E.2 T e ≤
      Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
        reconstructionSpatialWeight (e.1.position 0) := by
  have h := reconstruction_green_spatial_weight_bound hH hlam hLam A H E hE T e
  rw [← ofReal_integral_eq_lintegral_ofReal
    (reconstruction_green_spatial_integrable hH hlam hLam A H E hE T e)
    (Eventually.of_forall fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)] at h
  have hr : 0 ≤ Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
      reconstructionSpatialWeight (e.1.position 0) := by
    unfold reconstructionSpatialWeight
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp h

/-- The exponential velocity collar is integrable even though its ambient extension grows. -/
theorem reconstruction_green_collar_integrable (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun p => reconstructionCollarWeight H δ (p.velocity 0))
      (stripGreenOfKernel H K T e) := by
  have hm : Continuous (fun p : Point => reconstructionCollarWeight H δ (p.velocity 0)) :=
    (reconstructionCollarWeight_smooth H δ).continuous.comp
      ((continuous_apply 0).comp continuous_velocity)
  apply (integrable_const (2 : ℝ)).mono' hm.measurable.aestronglyMeasurable
  filter_upwards [stripGreenOfKernel_ae_mem_stripPast H K T e] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (reconstructionCollarWeight_nonneg _ _ _)]
  exact reconstructionCollarWeight_le_two H hδ ⟨hp.2.1.le, hp.2.2.le⟩

/-- The terminal time layer has actual Green mass at most its thickness. -/
theorem reconstruction_green_terminal_layer (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∫ p, (if T - δ < p.time then (1 : ℝ) else 0) ∂stripGreenOfKernel H K T e ≤ δ := by
  classical
  let J : Set Point := {p | p.time ∈ Ioo (T - δ) T}
  have hJ : MeasurableSet J := measurableSet_Ioo.preimage continuous_time.measurable
  have heq : (∫ p, (if T - δ < p.time then (1 : ℝ) else 0)
      ∂stripGreenOfKernel H K T e) = (stripGreenOfKernel H K T e).real J := by
    rw [← integral_indicator_one hJ]
    apply integral_congr_ae
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H K T e] with p hp
    simp only [J, indicator_apply, mem_ofPred, mem_Ioo, and_iff_left hp.1, Pi.one_apply]
  rw [heq]
  have hm := stripGreenOfKernel_timeMarginal H K T e (Ioo (T - δ) T) measurableSet_Ioo
  have hv : volume (Ioo (T - δ) T) = ENNReal.ofReal δ := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  rw [hv] at hm
  simpa only [Measure.real, ENNReal.toReal_ofReal hδ.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hm

/-- The integrated collar error is finite for the actual Green measure. -/
theorem reconstruction_green_error_integrable
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    {δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    Integrable (fun p => reconstructionErrorWeight H T δ R
      (KineticPoint.equivProd 1 (sectionTwoPoint p))) (stripGreenOfKernel H E.2 T e) := by
  classical
  have ht : Integrable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0)
      (stripGreenOfKernel H E.2 T e) := by
    have hm : Measurable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0) :=
      measurable_const.piecewise (measurableSet_lt measurable_const continuous_time.measurable)
        measurable_const
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun p => by split_ifs <;> norm_num
  exact (((reconstruction_green_collar_integrable H E.2 T e hδ).const_mul
    (Real.exp 1)).add ht).add
      ((reconstruction_green_spatial_integrable hH hlam hLam A H E hE T e).div_const R)

/-- Integrated localization error, with no unspecified analytic estimate. -/
theorem reconstruction_green_error_integral_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∫ p, reconstructionErrorWeight H T δ R
        (KineticPoint.equivProd 1 (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤
      Real.exp 1 * (2 * δ ^ 2 / lam) + δ +
        (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0)) / R := by
  classical
  have hc := reconstruction_green_collar_integrable H E.2 T e hδ
  have hs := reconstruction_green_spatial_integrable hH hlam hLam A H E hE T e
  have ht : Integrable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0)
      (stripGreenOfKernel H E.2 T e) := by
    have hm : Measurable (fun p : Point => if T - δ < p.time then (1 : ℝ) else 0) :=
      measurable_const.piecewise (measurableSet_lt measurable_const continuous_time.measurable)
        measurable_const
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun p => by split_ifs <;> norm_num
  change (∫ p, Real.exp 1 * reconstructionCollarWeight H δ (p.velocity 0) +
    (if T - δ < p.time then (1 : ℝ) else 0) + reconstructionSpatialWeight (p.position 0) / R
      ∂stripGreenOfKernel H E.2 T e) ≤ _
  have hadd₁ := integral_add (hc.const_mul (Real.exp 1)) ht
  have hadd₂ := integral_add ((hc.const_mul (Real.exp 1)).add ht) (hs.div_const R)
  simp only [Pi.add_apply] at hadd₁ hadd₂
  rw [hadd₂, hadd₁, integral_const_mul, integral_div]
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left
      (reconstruction_green_collar_bound hH hlam hLam A H E hE T e hδ) (Real.exp_pos _).le)
      (reconstruction_green_terminal_layer H E.2 T e hδ))
    (div_le_div_of_nonneg_right
      (reconstruction_green_spatial_integral_bound hH hlam hLam A H E hE T e) hR.le)

/-- A pointwise source approximation gives an explicit actual potential approximation. -/
theorem reconstruction_green_potential_error
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T a : ℝ) (e : StripPole H (T : WithTop ℝ))
    (ha : a ≤ e.1.time) (g f : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C)
    {δ R ε : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hgf : ∀ p, a ≤ p.time → |g p - f p| ≤ ε + C * reconstructionErrorWeight H T δ R
      (KineticPoint.equivProd 1 (sectionTwoPoint p))) :
    |stripPotentialOfKernel H E.2 T g e - stripPotentialOfKernel H E.2 T f e| ≤
      ε * (T - e.1.time) + C * (Real.exp 1 * (2 * δ ^ 2 / lam) + δ +
        (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
          reconstructionSpatialWeight (e.1.position 0)) / R) := by
  have hi := reconstruction_green_error_integrable hH hlam hLam A H E hE T e hδ R
  have hh := norm_integral_le_of_norm_le ((integrable_const ε).add (hi.const_mul C))
    (f := fun p => g p - f p) (by
      filter_upwards [reconstruction_green_ae_time_gt H E.2 T e] with p hp
      simpa only [Real.norm_eq_abs, Pi.add_apply] using! hgf p (ha.trans hp.le))
  rw [integral_sub (stripGreen_integrable_boundedBorel H E.2 T e g)
    (stripGreen_integrable_boundedBorel H E.2 T e f), Real.norm_eq_abs] at hh
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const ε) (hi.const_mul C), integral_const,
    integral_const_mul, smul_eq_mul] at hh
  have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ T - e.1.time := by
    have hT := (sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)).le
    simpa only [Measure.real, ENNReal.toReal_ofReal hT] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (stripGreenOfKernel_finite_time_mass H E.2 T e)
  exact hh.trans (add_le_add
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm hε)
    (mul_le_mul_of_nonneg_left
      (reconstruction_green_error_integral_bound hH hlam hLam A H E hE T e hδ hR) hC))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
