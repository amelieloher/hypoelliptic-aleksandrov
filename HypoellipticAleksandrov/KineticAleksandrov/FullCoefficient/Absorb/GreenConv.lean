module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.GreenSlices
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# `ρ^δ_ε = η_δ ⋆ (ν_·)_ε` for the Green measure
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam T : ℝ}

theorem greenDensity_eq_conv (hlam : 0 < lam) (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {ε : ℝ} (hε : 0 < ε) (τ : ℝ)
    (y : EvolutionAmbientState d) :
    greenDensity hlam η ε Γ τ y =
      ∫ s, η (τ - s) * greenSliceFun hlam K σ₀ p (S := ENNReal.ofReal T) ε y s := by
  have hfin : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  set Φ := flowKernelFamily (d := d) hlam with hΦ
  have hcont : Continuous fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      η (τ - x.1.1) * Φ.kernel ε (y - x.2) :=
    (hη.continuous.comp (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).mul
      ((Φ.contDiff hε).continuous.comp (continuous_const.sub continuous_snd))
  obtain ⟨Cη, hCη⟩ := hη.exists_bound
  obtain ⟨CΦ, hCΦ⟩ := abs_kernel_sub_le Φ hε
  have hint : Integrable (fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      η (τ - x.1.1) * Φ.kernel ε (y - x.2)) Γ := by
    refine Integrable.of_bound hcont.aestronglyMeasurable (Cη * CΦ)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCη _) (hCΦ y x.2) (abs_nonneg _) ((abs_nonneg _).trans (hCη 0))
  have h1 : greenDensity hlam η ε Γ τ y =
      ∫ x, η (τ - x.1.1) * Φ.kernel ε (y - x.2) ∂Γ := by
    unfold greenDensity smoothedDensity smoothDensity
    rw [integral_averagedSlice hη (continuous_kernel_sub Φ hε y).measurable]
    unfold greenPushforward
    rw [integral_map measurable_greenMap.aemeasurable]
    · exact (hη.continuous.comp (continuous_const.sub continuous_fst)).mul
        ((Φ.contDiff hε).continuous.comp (continuous_const.sub continuous_snd))
        |>.aestronglyMeasurable
  rw [h1]
  have hG := green_eq_compProd K σ₀ (ENNReal.ofReal T) p Γ hΓ
  rw [hG] at hint ⊢
  rw [Measure.integral_compProd hint]
  have h2 : ∀ a : ElapsedTime (ENNReal.ofReal T),
      ∫ w, η (τ - a.1) * Φ.kernel ε (y - w) ∂(sliceKernel K σ₀ p (ENNReal.ofReal T) a) =
        η (τ - a.1) * greenSliceFun hlam K σ₀ p (S := ENNReal.ofReal T) ε y a.1 := fun a => by
    rw [integral_const_mul, greenSliceFun_apply]; rfl
  simp only [h2]
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime (ENNReal.ofReal T))
  have hmap : (elapsedVolume (ENNReal.ofReal T)).map Subtype.val =
      volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal T} :=
    map_comap_subtype_coe (measurableSet_elapsedTime _) volume
  have hz : ∀ s ∈ ({τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal T})ᶜ,
      η (τ - s) * greenSliceFun hlam K σ₀ p (S := ENNReal.ofReal T) ε y s = 0 := fun s hs => by
    rw [greenSliceFun_apply_of_not hlam K σ₀ p ε y hs, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← hmap]
  exact (hemb.integral_map (fun s => η (τ - s) * greenSliceFun hlam K σ₀ p
    (S := ENNReal.ofReal T) ε y s)).symm

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
