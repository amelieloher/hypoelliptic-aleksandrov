module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization

/-! # Exact restriction from infinite to finite physical time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo
open scoped ENNReal

/-- A finite valid pole is also valid for the infinite terminal horizon. -/
def stripPoleInfinite (H : Interval) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    StripPole H ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩

/-- Truncating the actual infinite-horizon Green measure gives the finite-horizon measure. -/
theorem stripGreenOfKernel_horizonRestriction (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H K T e =
      (stripGreenOfKernel H K ⊤ (stripPoleInfinite H T e)).restrict {p | p.time < T} := by
  let R := ENNReal.ofReal (T - e.1.time)
  have hR : 0 < T - e.1.time := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
  have hh := greenMeasure_horizonRestriction K e.1.time R ⊤ le_top
    (Measure.dirac (stripPoleState H T e))
    (greenMeasure K e.1.time R (stripHorizon_pos H T e) _)
    (greenMeasure K e.1.time ⊤ ENNReal.zero_lt_top _)
    (greenMeasure_spec K _ _ _ _) (greenMeasure_spec K _ _ _ _)
  have hm : Measurable (fun q : ElapsedTime R × EvolutionAmbientState 1 =>
      (elapsedInclusion (show R ≤ ⊤ from le_top) q.1, q.2)) :=
    ((measurable_elapsedInclusion le_top).comp measurable_fst).prodMk measurable_snd
  have hs : {q : ElapsedTime ⊤ × EvolutionAmbientState 1 | ENNReal.ofReal q.1.1 < R} =
      elapsedPhysicalPoint e.1.time ⁻¹' {p : Point | p.time < T} := by
    ext q
    change ENNReal.ofReal q.1.1 < ENNReal.ofReal (T - e.1.time) ↔ e.1.time + q.1.1 < T
    rw [ENNReal.ofReal_lt_ofReal_iff hR]
    constructor <;> intro h <;> linarith
  have hh' := congrArg (fun μ => μ.map (elapsedPhysicalPoint e.1.time)) hh
  rw [Measure.map_map (measurable_elapsedPhysicalPoint _ _) hm, hs,
    ← Measure.restrict_map (measurable_elapsedPhysicalPoint _ _)
      (show MeasurableSet {p : Point | p.time < T} from
        (isOpen_Iio.preimage continuous_time).measurableSet)] at hh'
  exact hh'

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
