module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization

/-! # Physical-time marginals of the killed strip Green measure

The constant is exactly one and the statement covers every measurable time set and both
finite and infinite horizons. No source-time lower endpoint enters the construction.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- Restricting elapsed times can only decrease the Lebesgue mass of an absolute-time set. -/
theorem elapsedVolume_absoluteTime_le (R : ℝ≥0∞) (s : ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    elapsedVolume R {τ | s + τ.1 ∈ J} ≤ volume J := by
  have hm : Measurable (fun τ : ElapsedTime R => s + τ.1) :=
    measurable_const.add measurable_subtype_coe
  rw [elapsedVolume_apply R _
    (show MeasurableSet {τ : ElapsedTime R | s + τ.1 ∈ J} from hm hJ)]
  calc
    _ ≤ volume ((fun t : ℝ => s + t) ⁻¹' J) := by
      apply measure_mono
      rintro t ⟨τ, hτ, rfl⟩
      exact hτ
    _ = volume J := by
      rw [← Measure.map_apply
        (show Measurable (fun t : ℝ => s + t) from measurable_const.add measurable_id) hJ,
        map_add_left_eq_self]

/-- The literal killed kernel has physical-time marginal at most Lebesgue measure. -/
theorem stripGreenOfKernel_timeMarginal (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : WithTop ℝ) (e : StripPole H T) (J : Set ℝ) (hJ : MeasurableSet J) :
    stripGreenOfKernel H K T e {p | p.time ∈ J} ≤ volume J := by
  have hm : Measurable (fun τ : ElapsedTime (stripHorizon T e.1.time) =>
      e.1.time + τ.1) := measurable_const.add measurable_subtype_coe
  rw [stripGreenOfKernel, Measure.map_apply (measurable_elapsedPhysicalPoint _ _)
    (show MeasurableSet {p : Point | p.time ∈ J} from
      hJ.preimage continuous_time.measurable)]
  change greenMeasure K e.1.time _ _ (Measure.dirac (stripPoleState H T e))
    (Prod.fst ⁻¹' {τ | e.1.time + τ.1 ∈ J}) ≤ volume J
  calc
    _ ≤ (Measure.dirac (stripPoleState H T e)) univ *
        elapsedVolume (stripHorizon T e.1.time) {τ | e.1.time + τ.1 ∈ J} :=
      greenMeasure_timeMarginal_le K e.1.time _ _ _
        (greenMeasure_spec K _ _ _ _) _ (hm hJ)
    _ = elapsedVolume (stripHorizon T e.1.time) {τ | e.1.time + τ.1 ∈ J} := by
      simp only [Measure.dirac_apply_of_mem (mem_univ _), one_mul]
    _ ≤ volume J := elapsedVolume_absoluteTime_le _ _ J hJ

/-- The canonical autonomous strip Green measure has the exact constant-one time bound. -/
theorem stripGreen_timeMarginal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (e : StripPole H T) (J : Set ℝ) (hJ : MeasurableSet J) :
    stripGreen hH hLE hlam hLam A H T e {p | p.time ∈ J} ≤ volume J :=
  stripGreenOfKernel_timeMarginal H _ T e J hJ

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
