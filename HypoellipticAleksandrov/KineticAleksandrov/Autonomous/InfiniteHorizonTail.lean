module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMoment
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonSupport

/-! # Uniform finite-exit tail control from the exact exit-time moment -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The physical exit time is integrable on its genuine finite future slab. -/
theorem infinite_finite_exit_time_integrable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    Integrable (fun p : Point => p.time) (stripExit hH hLE hlam hLam A H T e) := by
  apply Integrable.mono' (integrable_const (max |e.1.time| |T|))
    continuous_time.measurable.aestronglyMeasurable
  filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T e] with p hp
  rw [Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hp.1),
      hp.2.1.trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- The true finite-exit tail is controlled uniformly in the terminal horizon. -/
theorem infinite_finite_exit_tail_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (R : ℝ) (hR : e.1.time < R) :
    (stripExit hH hLE hlam hLam A H T e).real {p | R ≤ p.time} ≤
      ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) /
        (R - e.1.time) := by
  let μ := stripExit hH hLE hlam hLam A H T e
  let S : Set Point := {p | R ≤ p.time}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_time.measurable
  have ht := infinite_finite_exit_time_integrable hH hLE hlam hLam A H T e
  have he : Integrable (fun p : Point => p.time - e.1.time) μ := ht.sub (integrable_const _)
  have hi : Integrable (S.indicator (fun _ : Point => R - e.1.time)) μ :=
    (integrable_const _).indicator hS
  have hn : S.indicator (fun _ : Point => R - e.1.time) ≤ᵐ[μ]
      fun p => p.time - e.1.time := by
    filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A H _
      (stripEvolution_spec hH hLE hlam hLam A H) T e] with p hp
    by_cases hs : p ∈ S
    · rw [indicator_of_mem hs]
      exact sub_le_sub_right hs _
    · rw [indicator_of_notMem hs]
      exact sub_nonneg.mpr hp.1
  have hle := integral_mono_ae hi he hn
  rw [integral_indicator hS, setIntegral_const, integral_sub ht (integrable_const _)] at hle
  have hmean := nested_exit_time_integral hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T e
  change (∫ p, p.time ∂μ) = e.1.time +
    (stripGreen hH hLE hlam hLam A H T e univ).toReal at hmean
  simp only [integral_const, Measure.real, stripExit_mass_one, ENNReal.toReal_one, smul_eq_mul,
    one_mul] at hle
  rw [hmean] at hle
  have hq : 0 ≤ (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le)
      (sub_nonneg.mpr e.2.2.2.le)) (by positivity)
  have hmass := ENNReal.toReal_le_of_le_ofReal hq
    (stripGreen_quadratic_mass hH hLE hlam hLam A H T e)
  apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
  change (μ S).toReal * (R - e.1.time) ≤ _
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
