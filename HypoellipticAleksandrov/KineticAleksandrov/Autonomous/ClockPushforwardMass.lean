module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardInfiniteTests

/-! # Finite masses of the actual measures in the clock pushforward identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- The actual normalized infinite Green measure has finite mass, by the interval density
  estimate. -/
instance clockNativeGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure (clockNativeGreen hH hLE hlam hLam A c e he) := by
  obtain ⟨C, -, hc⟩ := Interval.interval_green_finite_mass hH hLE
    (3 * lam / 5) (3 * Lam) (9 / 25) 9 (3 / 2) (by positivity) (by norm_num)
  have hh := @hc (-3 / 4) (3 / 4) (by norm_num)
    (c.extendedCoefficient lam A.a e) c.extendedVectorDrift
    (c.extended_sourceSetting hlam hLam A e)
    (intervalDomain_measurable clockNormalizedInterval)
    (clockEvolution hH hLE hlam hLam A c e).1
    (clockEvolution hH hLE hlam hLam A c e).2
    (clockEvolution_spec hH hLE hlam hLam A c e) (by norm_num) 0
    (Measure.dirac (clockInitialState c e he)) isFiniteMeasure_dirac
    (clockNativeGreen hH hLE hlam hLam A c e he)
    (clockNativeGreen_spec hH hLE hlam hLam A c e he)
  exact ⟨hh.2⟩

/-- Finite mass survives the established physical coordinate map. -/
instance clockGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure (clockGreen hH hLE hlam hLam A c e he) := by
  unfold clockGreen
  infer_instance

/-- The physical velocity weight is Borel. -/
theorem clock_velocity_weight_measurable :
    Measurable (fun p : Point => ENNReal.ofReal |p.velocity 0|) :=
  (((continuous_apply 0).comp continuous_velocity).abs.measurable).ennreal_ofReal

/-- The actual physical infinite Green has finite mass after weighting by velocity. -/
instance clockWeightedGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsFiniteMeasure ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt
    (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (3 * |c.vbar| / 2)) ?_) ?_
  · filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
    exact ENNReal.ofReal_le_ofReal (c.active_abs_bounds hp.2).2
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
