module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardSupport

/-! # The exact weighted pushforward identity for the actual killed Green measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal NNReal

/-- The literal position clock pushes velocity-weighted physical Green to the actual normalized
Green with factor exactly `|vbar| r²`. No density or analytic bridge is a premise. -/
theorem clock_green_pushforward
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure.map (c.map e) ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ENNReal.ofReal (|c.vbar| * c.r ^ 2) • clockGreen hH hLE hlam hLam A c e he := by
  have hD : 0 < |c.vbar| * c.r ^ 2 :=
    mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)
  have : IsFiniteMeasure ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) :=
    clockWeightedGreen_isFiniteMeasure hH hLE hlam hLam A c e he
  have := Measure.isFiniteMeasure_map
    ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) (c.map e)
  have := Measure.smul_finite (clockGreen hH hLE hlam hLam A c e he)
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (|c.vbar| * c.r ^ 2) ≠ ⊤)
  apply nested_physical_measure_eq clockGreenSupport isOpen_clockGreenSupport
    (clock_weighted_pushforward_ae_support hH hLE hlam hLam A c e he)
    (Measure.ae_smul_measure (clockGreen_ae_support hH hLE hlam hLam A c e he) _)
  intro f hs hn
  have hmap := integral_map
    (μ := (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) (c.continuous_map e).measurable.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable
  have hweight := integral_withDensity_eq_integral_toReal_smul
    (μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩)
    clock_velocity_weight_measurable
    (Filter.Eventually.of_forall (fun p : Point => ENNReal.ofReal_lt_top))
    (fun p => exitProbePhysical f (c.map e p))
  have hweight' : (∫ p, exitProbePhysical f (c.map e p)
      ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩ := by
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, clockWeightedProbe]
      using hweight
  exact hmap.trans (hweight'.trans ((clock_weighted_test_infinite hH hLE hlam hLam A c e he
    f hn hs).trans (by rw [integral_smul_measure, ENNReal.toReal_ofReal hD.le]; rfl)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
