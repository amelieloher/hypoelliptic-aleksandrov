module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandArrivalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandMixture

/-! # The actual core Green kernel and internal first-arrival measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- The native strip Green kernel restricted to the source closed core. -/
def belowFour_coreGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (T : ℝ) :
    Kernel (StripPole H (T : WithTop ℝ)) Point where
  toFun e := (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core}
  measurable' := nested_measurable_family_restrict _
    (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H T B hB)) _
    (isClosed_Icc.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Uniform quadratic strip mass makes the native core Green family a finite kernel. -/
instance belowFour_coreGreenKernel_isFinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (T : ℝ) :
    IsFiniteKernel (belowFour_coreGreenKernel hH hLE hlam hLam A c H T) := by
  refine ⟨ENNReal.ofReal ((H.hi - H.lo) ^ 2 / (2 * lam)), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  apply (Measure.restrict_le_self (μ := stripGreen hH hLE hlam hLam A H T e)
    (s := {z | z.velocity 0 ∈ c.core}) univ).trans
  apply (stripGreen_quadratic_mass hH hLE hlam hLam A H T e).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff_of_pos_right (by linarith : 0 < 2 * lam)).2
  nlinarith only [sq_nonneg (e.1.velocity 0 - H.lo),
    sq_nonneg (H.hi - e.1.velocity 0), sq_nonneg (H.hi - H.lo)]

/-- The actual internal first-arrival pole measure has mass at most one. -/
theorem belowFour_restart_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (W H : Interval) (s T : ℝ)
    (e : StripPole W (T : WithTop ℝ)) (he : s ≤ e.1.time) :
    nestedIntervalRestartPoles hH hLE hlam hLam A W H s T e univ ≤ 1 := by
  have hm := congrArg (fun mu : Measure Point => mu univ)
    (nestedIntervalRestartPoles_map hH hLE hlam hLam A W H s T e)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] at hm
  rw [hm]
  exact (measure_mono (subset_univ _)).trans_eq
    (strip_exit_probability hH hLE hlam hLam A W s T e he).1

/-- The actual internal first-arrival poles lie on the smaller interval's internal face. -/
theorem belowFour_restart_ae_internal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (W H : Interval) (s T : ℝ)
    (e : StripPole W (T : WithTop ℝ)) :
    ∀ᵐ ep ∂nestedIntervalRestartPoles hH hLE hlam hLam A W H s T e,
      ep.1 ∈ nestedIntervalInternalExit W H s T := by
  have hp := ae_restrict_mem (μ := stripExit hH hLE hlam hLam A W T e)
    (measurableSet_nestedIntervalInternalExit W H s T)
  rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A W H s T e] at hp
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H T)).ae_map_iff).mp hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
