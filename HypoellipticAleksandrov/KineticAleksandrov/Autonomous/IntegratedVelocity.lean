module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityAction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityMoments
import Mathlib.Tactic

/-! # Uniform velocity occupation and quadratic moment

This is the source node `l:timed-entrance#integrated-velocity` for smooth autonomous
coefficients. The band test is the literal bounded Borel indicator under the actual semigroup.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- Source occupation bound for any realizing full-space evolution. -/
theorem velocity_occupation_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z) :
    (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤
      (64 * Real.sqrt (2 * Lam) / lam) * r * Real.sqrt T := by
  have hLn : 0 ≤ Lam := hlam.le.trans hLam
  have h := velocityGreenRaw_band_mass_le hH hlam hLam A E hE hr hT z
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hb
  have ha : (∫ t in Ioc 0 T, velocityBandAction E r t z) =
      (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => velocityBandAction_eq_probability A E hE r t z
  rw [ha, velocity_band_integral_eq_green E hT r z]
  apply hb.trans_eq
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
  ring

/-- Uniform constant, actual measurable band occupation, and sharp real quadratic moment.
Only the named Hörmander and Lieberman construction inputs remain explicit. -/
theorem velocity_occupation_and_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r T : ℝ) (z : Z),
      0 < r → 0 < T →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤ C * r * Real.sqrt T ∧
        (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E (Real.toNNReal T) z) ≤ 2 * Lam * T := by
  refine ⟨64 * Real.sqrt (2 * Lam) / lam, ?_, ?_⟩
  · have hLp : 0 < Lam := hlam.trans_le hLam
    positivity
  · intro A r T z hr hT
    let E := fullSpaceEvolution hH hLE hlam hLam A
    have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
    refine ⟨velocity_occupation_le hH hlam hLam A E hE hr hT z, ?_⟩
    have hm := velocity_moment_le hlam A E hE (Real.toNNReal T) z
    simpa only [Real.coe_toNNReal T hT.le] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
