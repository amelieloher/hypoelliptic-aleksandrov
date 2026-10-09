module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Bounds

/-!
# The weighted smoothing `∫ (1 + |y - y'|)² Φ_h(y - y') dm(y')`

Every integrand of the smoothing estimates is bounded by a constant times this single function. This
module proves the bounds of the smoothed weighted measures and of their
first and second coordinate partials by it, using the derivative bounds of the Gaussian flow
estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

/-- The weighted kernel `(1 + |z|)² Φ_h(z)`. -/
def weight2 (h : ℝ) (z : EvolutionAmbientState d) : ℝ := (1 + ‖z‖) ^ 2 * Φ.kernel h z

/-- The `m`-smoothing of the weighted kernel. -/
def smoothWeight2 (h : ℝ) (m : Measure (EvolutionAmbientState d)) (y : EvolutionAmbientState d) :
    ℝ :=
  ∫ a, weight2 Φ h (y - a) ∂m

variable {Φ} {h : ℝ}

theorem weight2_nonneg (hh : 0 < h) (z : EvolutionAmbientState d) : 0 ≤ weight2 Φ h z :=
  (mul_pos (by positivity) (Φ.pos hh z)).le

theorem continuous_weight2 (hh : 0 < h) : Continuous (weight2 Φ h) :=
  ((continuous_const.add continuous_norm).pow 2).mul (Φ.contDiff hh).continuous

theorem kernel_le_weight2 (hh : 0 < h) (z : EvolutionAmbientState d) :
    Φ.kernel h z ≤ weight2 Φ h z := by
  have hp := Φ.pos hh z
  have : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  unfold weight2; nlinarith

theorem integrable_weight2 (hh : 0 < h) : Integrable (weight2 Φ h) :=
  Φ.weight_integrable 2 hh

theorem exists_weight2_bound (hh : 0 < h) : ∃ W : ℝ, ∀ z, weight2 Φ h z ≤ W := by
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨W, hW⟩ := Φ.weight_le 2 hK hsub
  exact ⟨W, fun z => hW h rfl z⟩

variable (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

theorem integrable_weight2_translate (hh : 0 < h) (y : EvolutionAmbientState d) :
    Integrable (fun a => weight2 Φ h (y - a)) m := by
  obtain ⟨W, hW⟩ := exists_weight2_bound (Φ := Φ) hh
  refine Integrable.of_bound (C := W) ((continuous_weight2 hh).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (weight2_nonneg hh _)]
  exact hW _

theorem smoothDensity_le_smoothWeight2 (hh : 0 < h) (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ≤ smoothWeight2 Φ h m y :=
  integral_mono (integrable_kernel_translate Φ m hh y) (integrable_weight2_translate m hh y)
    fun _ => kernel_le_weight2 hh _

omit [IsFiniteMeasure m] in
theorem smoothWeight2_nonneg (hh : 0 < h) (y : EvolutionAmbientState d) :
    0 ≤ smoothWeight2 Φ h m y :=
  integral_nonneg fun _ => weight2_nonneg hh _

theorem integrable_smoothWeight2 (hh : 0 < h) : Integrable (smoothWeight2 Φ h m) :=
  (integrable_smoothing_translate (integrable_weight2 hh) (continuous_weight2 hh) m).1

theorem integral_smoothWeight2 (hh : 0 < h) :
    ∫ y, smoothWeight2 Φ h m y = m.real Set.univ * ∫ z, weight2 Φ h z :=
  (integrable_smoothing_translate (integrable_weight2 hh) (continuous_weight2 hh) m).2

theorem continuous_smoothWeight2 (hh : 0 < h) : Continuous (smoothWeight2 Φ h m) := by
  have h0 := continuous_weight2 (Φ := Φ) hh
  obtain ⟨W, hW⟩ := exists_weight2_bound (Φ := Φ) hh
  unfold smoothWeight2
  refine continuous_of_dominated (bound := fun _ => W) (fun y => ?_) (fun y => ?_)
    (integrable_const _) ?_
  · exact ((h0.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weight2_nonneg hh _)]; exact hW _
  · exact Filter.Eventually.of_forall fun a => (h0.comp (continuous_id.sub continuous_const))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
