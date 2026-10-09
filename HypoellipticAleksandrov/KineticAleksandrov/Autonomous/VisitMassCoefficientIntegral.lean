module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenTest
import Mathlib.Tactic

/-! # Integrating the globally elliptic coefficient in the quadratic Green term -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The physical autonomous coefficient is continuous in native kinetic coordinates. -/
theorem visitCoefficient_continuous {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    Continuous (fun p : Point => A.a (p.position 0) (p.velocity 0)) :=
  A.smooth.continuous.comp
    (((continuous_apply 0).comp continuous_position).prodMk
      ((continuous_apply 0).comp continuous_velocity))

/-- The quadratic Green integrand is integrable against every finite physical measure. -/
theorem visitCoefficient_integrable {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun p => 2 * A.a (p.position 0) (p.velocity 0)) mu := by
  apply Integrable.mono' (integrable_const (2 * Lam))
    ((continuous_const.mul (visitCoefficient_continuous A)).measurable.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro p
  change ‖2 * A.a (p.position 0) (p.velocity 0)‖ ≤ 2 * Lam
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1])]
  nlinarith [(A.bounds (p.position 0) (p.velocity 0)).2]

/-- Ellipticity bounds the actual quadratic Green term by twice Lam times occupation mass. -/
theorem visitCoefficient_integral_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (mu : Measure Point) [IsFiniteMeasure mu] :
    (∫ p, 2 * A.a (p.position 0) (p.velocity 0) ∂mu) ≤ 2 * Lam * (mu univ).toReal := by
  have hi := integral_mono_ae (visitCoefficient_integrable hlam A mu)
    (integrable_const (2 * Lam))
    (Filter.Eventually.of_forall (fun p =>
      mul_le_mul_of_nonneg_left (A.bounds (p.position 0) (p.velocity 0)).2 (by norm_num)))
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
