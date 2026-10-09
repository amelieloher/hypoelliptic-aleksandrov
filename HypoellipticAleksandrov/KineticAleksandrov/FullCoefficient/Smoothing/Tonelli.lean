module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Integrating a smoothed function over phase space

For a finite measure `m` and an integrable continuous function `w` on phase space, the
`m`-smoothing `y ↦ ∫ w (y - a) dm(a)` is integrable with integral `m(ℝ^{2d}) ∫ w`
(Tonelli, using translation invariance of Lebesgue measure). This is the Tonelli step in the
Fisher-type and integrability bounds of the smoothing estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

local instance volumeIsAddHaarMeasurePhase (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (EvolutionAmbientState d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem integrable_smoothing_translate {w : EvolutionAmbientState d → ℝ}
    (hw : Integrable w) (hwc : Continuous w) (m : Measure (EvolutionAmbientState d))
    [IsFiniteMeasure m] :
    Integrable (fun y => ∫ a, w (y - a) ∂m) ∧
      ∫ y, ∫ a, w (y - a) ∂m = m.real Set.univ * ∫ y, w y := by
  have hcont : Continuous (fun p : EvolutionAmbientState d × EvolutionAmbientState d =>
      w (p.2 - p.1)) := hwc.comp (continuous_snd.sub continuous_fst)
  have hint : Integrable (fun p : EvolutionAmbientState d × EvolutionAmbientState d =>
      w (p.2 - p.1)) (m.prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun a => hw.comp_sub_right a, ?_⟩
    have : ∀ a : EvolutionAmbientState d, ∫ y, ‖w (y - a)‖ = ∫ y, ‖w y‖ := fun a =>
      integral_sub_right_eq_self (fun y => ‖w y‖) a
    simp only [this]
    exact integrable_const _
  refine ⟨hint.integral_prod_right, ?_⟩
  have hswap := integral_integral_swap (μ := m) (ν := (volume : Measure (EvolutionAmbientState d)))
    (f := fun a y => w (y - a)) hint
  rw [← hswap]
  have : ∀ a : EvolutionAmbientState d, ∫ y, w (y - a) = ∫ y, w y := fun a =>
    integral_sub_right_eq_self (fun y => w y) a
  simp only [this, integral_const, smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
