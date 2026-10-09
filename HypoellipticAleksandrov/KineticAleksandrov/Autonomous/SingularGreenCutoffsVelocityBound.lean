module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsRegularizedBarrier
import Mathlib.MeasureTheory.Group.Integral

/-! # Uniform actual first velocity jet of a position-smoothed homogeneous barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- Outside a fixed rectangle, every nonzero convolution summand has gauge at least one. -/
theorem barrier_convolution_far_gauge (eta : ℝ → ℝ) (S : ℝ)
    (hb : ∀ x ∈ tsupport eta, |x| < S) (q : ℝ × ℝ)
    (hq : S + 1 < |q.1| ∨ 1 ≤ |q.2|) (Y : ℝ) (hη : eta (q.1 - Y) ≠ 0) :
    1 ≤ bellmanGauge (Y, q.2) := by
  rcases hq with hx | hv
  · have he := hb (q.1 - Y) (subset_tsupport eta hη)
    have ht : |q.1| ≤ |q.1 - Y| + |Y| := by
      calc
        |q.1| = |q.1 - Y + Y| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hY : 1 ≤ |Y| := by linarith only [hx, he, ht]
    exact (Real.one_le_rpow hY (by norm_num : 0 ≤ (1 / 3 : ℝ))).trans
      (BarrierRegularization.barrier_position_gauge_lower (Y, q.2))
  · exact hv.trans (bellmanGauge_coordinate_bounds (Y, q.2)).2

/-- The actual regularized velocity derivative is bounded outside a fixed rectangle. -/
theorem barrier_smoothed_velocity_far {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    ∃ S Cv : ℝ, 0 < S ∧ 0 ≤ Cv ∧ ∀ q : ℝ × ℝ,
      S + 1 < |q.1| ∨ 1 ≤ |q.2| →
      |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Cv
        := by
  obtain ⟨S, hS, hbS⟩ := heta.2.1.isBounded.exists_pos_norm_lt
  have hbS' : ∀ x ∈ tsupport eta, |x| < S := by
    simpa only [Real.norm_eq_abs] using hbS
  obtain ⟨_, _, hv, _⟩ := h.origin_jet_bounds
  obtain ⟨Cv, hCv, hbv⟩ := hv
  refine ⟨S, Cv, hS, hCv, fun q hq => ?_⟩
  have hj := (barrier_position_convolution_velocity_jets h ha ha1 eta heta q.1 q.2).1
  rw [hj.deriv]
  have hi := position_kernel_integrable eta (fun Y => bellmanDv phi (Y, q.2))
    heta.1.continuous heta.2.1
    (barrier_velocity_fibers_locallyIntegrable h ha ha1 q.2).1 q.1
  have hηi : Integrable eta volume :=
    heta.1.continuous.integrable_of_hasCompactSupport heta.2.1
  have hbound (Y : ℝ) : |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| ≤
      eta (q.1 - Y) * Cv := by
    by_cases hη : eta (q.1 - Y) = 0
    · simp only [hη, zero_mul, abs_zero, le_refl]
    have hρ := barrier_convolution_far_gauge eta S hbS' q hq Y hη
    have hn := BarrierRegularization.barrier_gauge_one_ne_zero hρ
    have hv := (hbv (Y, q.2) hn).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hρ (by linarith)) hCv)
    rw [mul_one] at hv
    rw [abs_mul, abs_of_nonneg (heta.2.2.1 _)]
    exact mul_le_mul_of_nonneg_left hv (heta.2.2.1 _)
  unfold positionConvolution
  calc
    _ ≤ ∫ Y, |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| := abs_integral_le_integral_abs
    _ ≤ ∫ Y, eta (q.1 - Y) * Cv :=
      integral_mono hi.abs ((hηi.comp_sub_left q.1).mul_const Cv) hbound
    _ = Cv := by
      rw [integral_mul_const, integral_sub_left_eq_self, heta.2.2.2, one_mul]

/-- Position regularization has a global bounded actual velocity derivative.
The bound is proved from joint C² regularity on a compact rectangle and homogeneous decay
  outside. -/
theorem barrier_smoothed_velocity_bounded {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ q : ℝ × ℝ,
      |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Bv
        := by
  let f := positionConvolution eta (bellmanOriginExtension phi)
  have hf := barrier_position_regularization_joint h ha ha1 eta heta
  have hc : Continuous (fun q : ℝ × ℝ => (fderiv ℝ f q) (0, 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous.comp (hf.continuous_fderiv (by norm_num))
  have he (q : ℝ × ℝ) : deriv (fun v => f (q.1, v)) q.2 = (fderiv ℝ f q) (0, 1) :=
    (bellman_hasDerivAt_second (hf.differentiable (by norm_num) q)).deriv
  obtain ⟨S, Cv, hS, hCv, hbfar⟩ := barrier_smoothed_velocity_far h ha ha1 eta heta
  obtain ⟨B, hb⟩ := ((isCompact_Icc (a := -(S + 1)) (b := S + 1)).prod
    (isCompact_Icc (a := -1) (b := 1))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B Cv, hCv.trans (le_max_right _ _), fun q => ?_⟩
  by_cases hq : q ∈ Icc (-(S + 1)) (S + 1) ×ˢ Icc (-1) 1
  · rw [he q]
    have hqb : |(fderiv ℝ f q) (0, 1)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hb q hq
    exact hqb.trans (le_max_left _ _)
  · have hfar : S + 1 < |q.1| ∨ 1 ≤ |q.2| := by
      by_contra hn
      push Not at hn
      exact hq ⟨abs_le.mp hn.1, (abs_le.mp hn.2.le)⟩
    exact (hbfar q hfar).trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
