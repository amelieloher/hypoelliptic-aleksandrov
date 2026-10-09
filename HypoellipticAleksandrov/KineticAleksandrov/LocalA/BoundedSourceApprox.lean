module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Signed bounded-source Duhamel estimates

Contraction and integrability use the master kernel without source smoothness.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Sub-Markov contraction bounds a signed source integral in absolute value. -/
theorem abs_duhamelSourceIntegral_le (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (q : EvolutionQuery Ω γ) :
    |duhamelSourceIntegral K g q| ≤ M := by
  have hn : ‖duhamelSourceIntegral K g q‖ ≤ M * (K.master q).real univ := by
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      exact hgb _
  have hm : (K.master q).real univ ≤ 1 := by
    simpa only [Measure.real, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one q)
  rw [Real.norm_eq_abs] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left hm hM).trans_eq (mul_one M))

/-- Signed contraction also holds for the existing zero extension off the starting fiber. -/
theorem abs_duhamelIntegrand_le (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (p : KineticPoint d) (r : ℝ) :
    |duhamelIntegrand K g p r| ≤ M := by
  unfold duhamelIntegrand
  split
  · exact abs_duhamelSourceIntegral_le K g M hM hgb _
  · exact (abs_zero).le.trans hM

/-- A bounded Borel source has an integrable source-time integrand on finite intervals. -/
theorem integrableOn_duhamelIntegrand_bounded (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (g : KineticPoint d → ℝ)
    (hg : Measurable g) (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M)
    (p : KineticPoint d) (T : ℝ) :
    IntegrableOn (duhamelIntegrand K g p) (Ioc p.time T) := by
  have hm : Measurable (duhamelIntegrand K g p) :=
    (measurable_duhamelIntegrand K hΩ hγ g hg).comp
      (measurable_const.prodMk measurable_id)
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := M) ?_⟩
  exact Filter.Eventually.of_forall fun r => by
    rw [Real.norm_eq_abs]
    exact abs_duhamelIntegrand_le K g M hM hgb p r

/-- The finite-horizon Duhamel estimate holds for signed bounded sources. -/
theorem abs_duhamelPotential_le (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (p : KineticPoint d) (T : ℝ) (hp : p.time ≤ T) :
    |duhamelPotential K T g p| ≤ (T - p.time) * M := by
  have hn := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc p.time T)) (f := duhamelIntegrand K g p)
    (C := M) (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs]
      exact abs_duhamelIntegrand_le K g M hM hgb p r)
  change |∫ r, duhamelIntegrand K g p r ∂volume.restrict (Ioc p.time T)| ≤ _
  rw [Real.norm_eq_abs] at hn
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp), mul_comm] using hn

/-- An absolute time distance dominates the potential on the entire starting space. -/
theorem abs_duhamelPotential_le_abs_time (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (p : KineticPoint d) (T : ℝ) :
    |duhamelPotential K T g p| ≤ |T - p.time| * M := by
  by_cases hp : p.time ≤ T
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hp)] using
      abs_duhamelPotential_le K g M hM hgb p T hp
  · rw [duhamelPotential_eq_zero_of_terminal_le K T g p (le_of_not_ge hp), abs_zero]
    exact mul_nonneg (abs_nonneg _) hM

/-- The Duhamel integrand vanishes strictly before its starting time. -/
theorem duhamelIntegrand_eq_zero_of_lt_start (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d) {r : ℝ} (hr : r < p.time) :
    duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  exact dite_eq_right (fun h => (not_le_of_gt hr) h.1)

/-- Below-start source times contribute zero, and the diagonal has zero time measure. -/
theorem duhamelPotential_eq_integral_window (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d) {a T : ℝ} (ha : a ≤ p.time) :
    duhamelPotential K T g p = ∫ r in Ioo a T, duhamelIntegrand K g p r := by
  rw [duhamelPotential, integral_Ioc_eq_integral_Ioo]
  symm
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (fun r hr => ⟨ha.trans_lt hr.1, hr.2⟩)
  filter_upwards [(volume : Measure ℝ).ae_ne p.time] with r hne
  intro hr
  have hle : r ≤ p.time := le_of_not_gt (fun h => hr.2 ⟨h, hr.1.2⟩)
  exact duhamelIntegrand_eq_zero_of_lt_start K g p (lt_of_le_of_ne hle hne)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
