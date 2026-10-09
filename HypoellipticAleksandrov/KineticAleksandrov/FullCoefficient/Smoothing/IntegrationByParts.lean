module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Flux
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts in the phase variable

For smooth `g` with `g` and `∂_c g` integrable, `∫ ∂_c g = 0`; for a smooth bounded cut-off `ζ`
with bounded `∂_c ζ`, `∫ (∂_c g) ζ = - ∫ g ∂_c ζ`. For `SmoothW21 g`, all first and second
coordinate partials integrate to zero. Used in the energy identities, with the coordinate partials
`velocityPartial` and `positionPartial` of `Calculus.lean`
(`coordPartial (inl i) = velocityPartial i`, `coordPartial (inr i) = positionPartial i`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

local instance volumeIsAddHaarMeasurePhase' (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (EvolutionAmbientState d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Integration by parts against a smooth bounded cut-off with bounded derivative:
`∫ ζ ∂_c g = - ∫ (∂_c ζ) g`. -/
theorem integral_mul_coordPartial_eq_neg {ζ g : EvolutionAmbientState d → ℝ}
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

/-- `∫ ∂_c g = 0` for smooth `g` with `g` and `∂_c g` integrable. -/
theorem integral_coordPartial_eq_zero {g : EvolutionAmbientState d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : Fin d ⊕ Fin d) (hgi : Integrable g)
    (hgdi : Integrable (coordPartial c g)) : ∫ y, coordPartial c g y = 0 := by
  have := integral_mul_coordPartial_eq_neg (ζ := fun _ => 1) contDiff_const hg (A := 1)
    (fun _ => by simp) c (B := 0) (fun y => by simp [coordPartial_const_apply]) hgi hgdi
  simpa [coordPartial_const_apply] using this

/-- For `SmoothW21 g`, every first coordinate partial integrates to zero. -/
theorem SmoothW21.integral_coordPartial {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (c : Fin d ⊕ Fin d) : ∫ y, coordPartial c g y = 0 :=
  integral_coordPartial_eq_zero hg.1 c hg.2.1 (hg.2.2.1 c)

/-- For `SmoothW21 g`, every second coordinate partial integrates to zero. -/
theorem SmoothW21.integral_coordPartial₂ {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (c c' : Fin d ⊕ Fin d) : ∫ y, coordPartial c' (coordPartial c g) y = 0 :=
  integral_coordPartial_eq_zero (contDiff_coordPartial hg.1 c) c' (hg.2.2.1 c)
    (hg.2.2.2 c c')

/-- Velocity-partial form of `SmoothW21.integral_coordPartial`. -/
theorem SmoothW21.integral_velocityPartial {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (i : Fin d) : ∫ y, velocityPartial i g y = 0 :=
  hg.integral_coordPartial (Sum.inl i)

/-- Position-partial form of `SmoothW21.integral_coordPartial`. -/
theorem SmoothW21.integral_positionPartial {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (i : Fin d) : ∫ y, positionPartial i g y = 0 :=
  hg.integral_coordPartial (Sum.inr i)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
