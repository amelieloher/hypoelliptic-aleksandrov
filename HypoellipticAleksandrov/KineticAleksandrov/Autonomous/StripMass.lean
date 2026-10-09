module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization

/-! # Finite-horizon mass of the physical killed Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- Finite time bounds the actual killed Green measure, without a normalization factor. -/
theorem stripGreenOfKernel_finite_time_mass (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H K T e univ ≤ ENNReal.ofReal (T - e.1.time) := by
  have hR : 0 < T - e.1.time := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
  rw [stripGreenOfKernel, Measure.map_apply (measurable_elapsedPhysicalPoint _ _)
    MeasurableSet.univ, preimage_univ]
  have h := greenMeasure_mass_le K e.1.time (T - e.1.time) hR
    (Measure.dirac (stripPoleState H T e)) _
    (greenMeasure_spec K e.1.time _ (stripHorizon_pos H T e) _)
  simpa only [Measure.dirac_apply_of_mem (mem_univ _), one_mul] using! h

/-- The finite-time mass bound for the unique autonomous killed family. -/
theorem stripGreen_finite_time_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    stripGreen hH hLE hlam hLam A H T e univ ≤ ENNReal.ofReal (T - e.1.time) :=
  stripGreenOfKernel_finite_time_mass H _ T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
