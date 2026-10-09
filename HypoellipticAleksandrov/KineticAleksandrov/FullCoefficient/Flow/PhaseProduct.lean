module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Defs
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Gaussian2D
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product functions on phase space

A function `y ↦ ∏ i, f (y.1 i, y.2 i)` on `EvolutionAmbientState d = Vec d × Vec d` is integrable
when `f` is integrable on `ℝ × ℝ`, and its integral is `(∫ f) ^ d`. This is the coordinate
independence used to reduce the Gaussian flow to the two-dimensional factor `φ_h`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem integrable_phase_prod {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun y : EvolutionAmbientState d => ∏ i, f (y.1 i, y.2 i)) := by
  have hmp := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)
  rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have := Integrable.fintype_prod (ι := Fin d) (μ := fun _ => (volume : Measure (ℝ × ℝ)))
    (f := fun _ => f) (fun _ => hf)
  convert this using 2
  simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

theorem integral_phase_prod (f : ℝ × ℝ → ℝ) :
    ∫ y : EvolutionAmbientState d, ∏ i, f (y.1 i, y.2 i) = (∫ p, f p) ^ d := by
  have hmp := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)
  rw [← hmp.integral_comp']
  have := integral_fintype_prod_volume_eq_pow (ι := Fin d) f
  simpa [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
