module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.GreenConv
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.MollFamily

/-!
# Almost-everywhere convergence of the mollified Green densities

for fixed `ε`, the
time mollifications `ρ^{δ_n}_ε(τ, y)` converge to `(ν_τ)_ε(y)` for almost every `(τ, y)`:
for each `y` this is the Lebesgue differentiation theorem in `τ`, and the exceptional set is
measurable, so Tonelli applies.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory Filter Topology
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam T : ℝ}

theorem locallyIntegrable_greenSliceFun (hlam : 0 < lam)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)) (σ₀ : ℝ) (hT : 0 < T)
    (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀) {ε : ℝ} (hε : 0 < ε)
    (y : EvolutionAmbientState d) :
    LocallyIntegrable (greenSliceFun hlam K σ₀ p (S := ENNReal.ofReal T) ε y) volume := by
  set R : ℝ := (flowKernelFamily (d := d) hlam).supConst * (ε ^ (2 * d))⁻¹ with hR
  have hR0 : 0 ≤ R := mul_nonneg (supConst_nonneg _ hε) (by positivity)
  have hcar : {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal T} ⊆ Set.Ioo 0 T := by
    intro s ⟨h1, h2⟩
    exact ⟨h1, (ENNReal.ofReal_lt_ofReal_iff hT).1 h2⟩
  have hb : Integrable (Set.indicator (Set.Ioo 0 T) fun _ => R) := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const (by simp)
  refine Integrable.locallyIntegrable (hb.mono'
    (measurable_greenSliceFun hlam K σ₀ p hε y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_))
  by_cases hs : 0 < s ∧ ENNReal.ofReal s < ENNReal.ofReal T
  · have hsT := hcar hs
    rw [Set.indicator_of_mem hsT, Real.norm_eq_abs]
    have := greenSliceFun_apply hlam K σ₀ p (S := ENNReal.ofReal T) ε y ⟨s, hs⟩
    simp only at this
    rw [this, abs_of_nonneg (smoothDensity_nonneg _ _ hε y)]
    refine (smoothDensity_le _ _ hε y).trans ?_
    calc _ ≤ (flowKernelFamily (d := d) hlam).supConst * (ε ^ (2 * d))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (sliceMeasure_real_univ_le K σ₀ p ⟨s, hs⟩) hR0
      _ = R := mul_one _
  · rw [greenSliceFun_apply_of_not hlam K σ₀ p ε y hs]
    simp only [norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hR0) s

theorem ae_tendsto_greenDensity (hlam : 0 < lam)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)) (σ₀ : ℝ) (hT : 0 < T)
    (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))),
      Tendsto (fun n => greenDensity hlam (mollN n) ε Γ x.1.1 x.2) atTop
        (𝓝 (smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2)) := by
  have hfin : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  have hfm : ∀ n, Measurable fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      greenDensity hlam (mollN n) ε Γ x.1.1 x.2 := by
    intro n
    have hc : Continuous fun p : ℝ × EvolutionAmbientState d =>
        greenDensity hlam (mollN n) ε Γ p.1 p.2 :=
      (contDiff_greenDensity hlam Γ (isMollifier_mollN n) hε).continuous
    have hg := measurable_greenMap (S := ENNReal.ofReal T) (d := d)
    have := hc.measurable.comp hg
    exact this
  have hρm : Measurable fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2 := by
    have h1 := measurable_ofReal_smoothDensity (Φ := flowKernelFamily (d := d) hlam) hε
      (sliceKernel K σ₀ p (ENNReal.ofReal T))
    have h3 := h1.ennreal_toReal
    have e : (fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
        smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2) =
        fun x => (ENNReal.ofReal (smoothDensity (flowKernelFamily (d := d) hlam) ε
          (sliceKernel K σ₀ p (ENNReal.ofReal T) x.1) x.2)).toReal :=
      funext fun x => (ENNReal.toReal_ofReal (smoothDensity_nonneg _ _ hε _)).symm
    rw [e]; exact h3
  set N : Set (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d) :=
    {x | ¬ Tendsto (fun n => greenDensity hlam (mollN n) ε Γ x.1.1 x.2 -
      smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2) atTop
      (𝓝 0)} with hN
  have hNm : MeasurableSet N :=
    (measurableSet_tendsto (𝓝 0) (fun n => (hfm n).sub hρm)).compl
  have hN0 : ((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d)))
      N = 0 := by
    rw [Measure.prod_apply_symm hNm]
    have hy : ∀ y : EvolutionAmbientState d, elapsedVolume (ENNReal.ofReal T)
        ((fun a => (a, y)) ⁻¹' N) = 0 := by
      intro y
      have hsm : MeasurableSet ((fun a : ElapsedTime (ENNReal.ofReal T) => (a, y)) ⁻¹' N) :=
        (measurable_id.prodMk measurable_const) hNm
      rw [elapsedVolume_apply _ _ hsm]
      have hloc := locallyIntegrable_greenSliceFun hlam K σ₀ hT p hε y
      have hnull := ae_tendsto_mollify hloc
      rw [ae_iff] at hnull
      refine measure_mono_null ?_ hnull
      rintro τ ⟨a, ha, rfl⟩ hconv
      apply ha
      have hconv' : Tendsto (fun n => greenDensity hlam (mollN n) ε Γ a.1 y) atTop
          (𝓝 (smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p a) y)) := by
        have e1 : ∀ n, greenDensity hlam (mollN n) ε Γ a.1 y =
            ∫ s, mollN n (a.1 - s) * greenSliceFun hlam K σ₀ p (S := ENNReal.ofReal T) ε y s :=
          fun n => greenDensity_eq_conv hlam K σ₀ hT p Γ hΓ (isMollifier_mollN n) hε a.1 y
        have e2 := greenSliceFun_apply hlam K σ₀ p (S := ENNReal.ofReal T) ε y a
        simp only [e1]
        rw [← e2]
        exact hconv
      exact (tendsto_sub_nhds_zero_iff.2 hconv')
    simp only [hy, lintegral_zero]
  have : ∀ᵐ x ∂((elapsedVolume (ENNReal.ofReal T)).prod
      (volume : Measure (EvolutionAmbientState d))), x ∉ N := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => not_not.1 hx) hN0
  filter_upwards [this] with x hx
  have hx' : Tendsto (fun n => greenDensity hlam (mollN n) ε Γ x.1.1 x.2 -
      smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2) atTop
      (𝓝 0) := not_not.1 hx
  exact tendsto_sub_nhds_zero_iff.1 hx'

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
