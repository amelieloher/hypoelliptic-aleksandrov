module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyPhysicalSemigroup
import Mathlib.Tactic

/-! # The velocity band as a bounded Borel semigroup test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open SectionTwo

/-- The literal unit indicator of the physical velocity band. -/
def velocityBandDatum (r : ℝ) : BoundedBorel (EvolutionAmbientState 1) := by
  let B : Set (EvolutionAmbientState 1) := {w | |w.2 0| ≤ 3 * r}
  have hB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_snd))
    measurable_const
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : |w.2 0| ≤ 3 * r <;> simp [B, Set.indicator, hw]⟩⟩

/-- The source band test evaluated by the actual physical semigroup. -/
def velocityBandAction (E : FullSpaceEvolution) (r t : ℝ) (z : Z) : ℝ :=
  fullSpacePhysicalSemigroup E (Real.toNNReal t) (velocityBandDatum r)
    (fun _ => z.1, fun _ => z.2)

/-- The semigroup band action is exactly the real transition probability. -/
theorem velocityBandAction_eq_probability {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (r t : ℝ) (z : Z) :
    velocityBandAction E r t z = (velocityBandProbability E r z t).toReal := by
  rw [velocityBandAction, fullSpacePhysicalSemigroup_eq_action A E hE,
    fullSpaceAction_eq_zeroTime A E hE _ _ (Real.toNNReal t).property]
  have : IsFiniteMeasure (E.2.master (wholeQuery (Real.toNNReal t) z)) :=
    ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  change (∫ w, (velocityNativeBand r).indicator (fun _ => (1 : ℝ)) w
    ∂E.2.master (wholeQuery (Real.toNNReal t) z)) = _
  rw [integral_indicator (velocityNativeBand_measurable r)]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, velocityBandProbability,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- In physical scalar coordinates the same probability is the band mass of `kernelXV`. -/
theorem velocityBandProbability_eq_kernelXV (E : FullSpaceEvolution) (r t : ℝ) (z : Z) :
    velocityBandProbability E r z t =
      kernelXV E (Real.toNNReal t) z {w | |w.2| ≤ 3 * r} := by
  rw [kernelXV, Measure.map_apply nativeToXV_measurable]
  · rfl
  · exact measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const

/-- The literal semigroup band test is integrable on every finite time interval. -/
theorem velocityBandAction_integrable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (r T : ℝ) (z : Z) :
    Integrable (fun t => velocityBandAction E r t z) (volume.restrict (Ioc 0 T)) := by
  have he : (fun t => velocityBandAction E r t z) =
      fun t => (velocityBandProbability E r z t).toReal :=
    funext fun t => velocityBandAction_eq_probability A E hE r t z
  rw [he]
  exact velocityBandProbability_toReal_integrable E r z T

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
