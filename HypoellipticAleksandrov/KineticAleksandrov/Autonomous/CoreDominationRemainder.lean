module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursion
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Vanishing individual masses in a finite counting measure -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology

/-- A finite sum of positive measures forces each individual total mass to tend to zero. -/
theorem visit_measure_mass_tendsto_zero (mu : ℕ → Measure Point)
    [IsFiniteMeasure (Measure.sum mu)] :
    Tendsto (fun n => mu n univ) atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [← Measure.sum_apply _ MeasurableSet.univ]
  exact measure_ne_top _ _

/-- Individual entrance masses vanish once the full counting measure is finite. -/
theorem visitGamma_mass_tendsto_zero (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : ProbabilityTheory.Kernel Point Point)
    [hfin : IsFiniteMeasure (visitStarts P I Sin Sout exitActive exitWaiting)] :
    Tendsto (fun n => visitGamma P I Sin Sout exitActive exitWaiting n univ) atTop
      (𝓝 0) := by
  have : IsFiniteMeasure
      (Measure.sum (visitGamma P I Sin Sout exitActive exitWaiting)) := by
    simpa only [visitStarts] using hfin
  exact visit_measure_mass_tendsto_zero _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
