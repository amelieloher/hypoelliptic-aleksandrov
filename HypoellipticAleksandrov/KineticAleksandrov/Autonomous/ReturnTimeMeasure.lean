module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator
import Mathlib.Tactic

/-! # The finite-measure Borel extension in the return-time argument

Smooth compact nonnegative tests suffice to compare finite terminal measures.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter

/-- Smooth nonnegative terminal-test comparison extends to every bounded Borel datum. -/
theorem return_measure_comparison (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      HasCompactSupport f → (∀ z, 0 ≤ f z) →
      (∫ z, f z ∂μ) ≤ C * ∫ z, f z ∂ν)
    (F : BoundedBorel (ℝ × ℝ)) (hF : ∀ z, 0 ≤ F z) :
    (∫ z, F z ∂μ) ≤ C * ∫ z, F z ∂ν := by
  let c := ENNReal.ofReal C
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (c • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top ν univ)⟩
  have horder : μ ≤ c • ν := by
    apply measure_le_of_smooth_integral_le isOpen_univ (by simp)
    intro f hs hf _ hfn
    simpa only [integral_smul_measure, c, ENNReal.toReal_ofReal hC, smul_eq_mul] using
      htest f hs hf hfn
  have hmono := integral_mono_measure horder (Eventually.of_forall hF)
    (integrable_boundedBorel F (c • ν))
  simpa only [integral_smul_measure, c, ENNReal.toReal_ofReal hC, smul_eq_mul] using hmono

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
