module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts against a cut-off

For a smooth bounded cut-off `ζ` with bounded `∂_c ζ`, and `g`, `∂_c g` integrable:
`∫ ζ ∂_c g = −∫ (∂_c ζ) g`. This is the form used by the energy inequality.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

local instance volumeIsAddHaarMeasurePhaseEnergy (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (EvolutionAmbientState d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Integration by parts against a smooth bounded cut-off with bounded derivative:
`∫ ζ ∂_c g = - ∫ (∂_c ζ) g`. -/
theorem integral_cutoff_mul_coordPartial_eq_neg {ζ g : EvolutionAmbientState d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {A B : ℝ}
    (hA : ∀ y, |ζ y| ≤ A) (c : Fin d ⊕ Fin d) (hB : ∀ y, |coordPartial c ζ y| ≤ B)
    (hgi : Integrable g) (hgdi : Integrable (coordPartial c g)) :
    ∫ y, ζ y * coordPartial c g y = - ∫ y, coordPartial c ζ y * g y := by
  have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have h1 : Integrable (fun y => fderiv ℝ ζ y (coordDir c) * g y) := by
    refine (hgi.norm.const_mul B).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_coordPartial hζ c).mul hg.continuous).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
  have h2 : Integrable (fun y => ζ y * fderiv ℝ g y (coordDir c)) := by
    refine (hgdi.norm.const_mul A).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hζ.continuous.mul (continuous_coordPartial hg c)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _)
  have h3 : Integrable (fun y => ζ y * g y) := by
    refine (hgi.norm.const_mul A).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hζ.continuous.mul hg.continuous).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := coordDir c) h1 h2 h3
    (fun x _ => hζd x) (fun x _ => hgd x)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
