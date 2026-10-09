module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DensityIntegral
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The evolved complex measure `η` and its total variation

Abstract measure theory behind the half-time evolution of Lemma 5.1: for a finite measure
`μ` on `X`, a finite kernel `κ : X → Y`, a unimodular measurable phase `ph : Y → ℂ` and a
measurable `π : Y → Z`, the complex measure `η = (((μ ⊗ₘ κ).snd).withDensityᵥ ph).map π` on `Z`
satisfies
* `‖∫ h dη‖ ≤ ∫ ‖h‖ d|η|` and `∫ᵛ h dη = ∫_μ ∫_{κ x} ph(y) h(π y)` for bounded Borel `h`;
* `|η|(Z) ≤ μ(X) · δ` whenever every fibre measure `((κ x).withDensityᵥ ph).map π` has total
  variation at most `δ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The complex measure of the half-time evolution. -/
def evolvedMeasure (μ : Measure X) (κ : ProbabilityTheory.Kernel X Y) (ph : Y → ℂ) (π : Y → Z) :
    VectorMeasure Z ℂ :=
  (((μ ⊗ₘ κ).snd).withDensityᵥ ph).map π

/-- The fibre measure at `x`. -/
def fibreMeasure (κ : ProbabilityTheory.Kernel X Y) (ph : Y → ℂ) (π : Y → Z) (x : X) :
    VectorMeasure Z ℂ :=
  ((κ x).withDensityᵥ ph).map π

variable (μ : Measure X) [IsFiniteMeasure μ] (κ : ProbabilityTheory.Kernel X Y)
  [ProbabilityTheory.IsFiniteKernel κ] (ph : Y → ℂ) (π : Y → Z)

/-- Integrals against the second marginal of a kernel product. -/
lemma integral_snd_compProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Y → E) (hf : Integrable f (μ ⊗ₘ κ).snd) :
    ∫ y, f y ∂(μ ⊗ₘ κ).snd = ∫ x, ∫ y, f y ∂κ x ∂μ := by
  have hsnd : Measurable (Prod.snd : X × Y → Y) := measurable_snd
  have hf' : Integrable (fun p : X × Y => f p.2) (μ ⊗ₘ κ) := by
    rw [Measure.snd] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable hsnd.aemeasurable).1 hf
  have hf'' : AEStronglyMeasurable f (Measure.map Prod.snd (μ ⊗ₘ κ)) := by
    rw [Measure.snd] at hf
    exact hf.aestronglyMeasurable
  rw [Measure.snd, integral_map hsnd.aemeasurable hf'', Measure.integral_compProd hf']


/-- Pairing of bounded Borel `h` with `η`, as an iterated kernel integral. -/
lemma evolved_integral (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (h : Z → ℂ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ z, ‖h z‖ ≤ C) :
    (∫ᵛ z, h z ∂[ContinuousLinearMap.mul ℝ ℂ; evolvedMeasure μ κ ph π]) =
      ∫ x, ∫ y, h (π y) * ph y ∂κ x ∂μ := by
  set Λ : Measure Y := (μ ⊗ₘ κ).snd with hΛ
  have hv : (Λ.withDensityᵥ ph).variation = Λ := variation_density_one Λ ph hph hph1
  have hi : Integrable (fun y : Y => h (π y)) Λ := by
    obtain ⟨C, hC⟩ := hb
    exact Integrable.mono' (integrable_const C) (hh.comp hπ).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hC (π y)))
  have hiv : (Λ.withDensityᵥ ph).Integrable (h ∘ π) := by
    simpa only [VectorMeasure.Integrable, hv, Function.comp_def] using hi
  unfold evolvedMeasure
  rw [VectorMeasure.integral_map hπ hh.aestronglyMeasurable hiv,
    integral_density_one Λ ph hph hph1 _ hi]
  exact integral_snd_compProd μ κ (fun y => h (π y) * ph y)
    (hi.mul_bdd hph.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => (hph1 y).le)))

/-- `‖∫ h dη‖ ≤ ∫ ‖h‖ d|η|`. -/
lemma evolved_integral_enorm_le (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (h : Z → ℂ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ z, ‖h z‖ ≤ C) :
    ‖∫ x, ∫ y, h (π y) * ph y ∂κ x ∂μ‖ₑ ≤ ∫⁻ z, ‖h z‖ₑ ∂(evolvedMeasure μ κ ph π).variation := by
  rw [← evolved_integral μ κ ph π hph hph1 hπ h hh hb]
  refine VectorMeasure.enorm_integral_le_lintegral_enorm.trans ?_
  have : ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  calc _ ≤ 1 * ∫⁻ z, ‖h z‖ₑ ∂(evolvedMeasure μ κ ph π).variation := by gcongr
    _ = _ := one_mul _


lemma integrable_phase_finite {W : Type*} [MeasurableSpace W] (ν : Measure W) [IsFiniteMeasure ν]
    (ph : W → ℂ) (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) : Integrable ph ν :=
  Integrable.mono' (integrable_const (1 : ℝ)) hph.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => (hph1 w).le))

lemma fibreMeasure_apply (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (x : X) {t : Set Z} (ht : MeasurableSet t) :
    fibreMeasure κ ph π x t = ∫ y, (π ⁻¹' t).indicator ph y ∂κ x := by
  unfold fibreMeasure
  rw [VectorMeasure.map_apply _ hπ ht, withDensityᵥ_apply (integrable_phase_finite _ ph hph hph1)
    (hπ ht), integral_indicator (hπ ht)]

lemma evolvedMeasure_apply (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    {t : Set Z} (ht : MeasurableSet t) :
    evolvedMeasure μ κ ph π t = ∫ x, ∫ y, (π ⁻¹' t).indicator ph y ∂κ x ∂μ := by
  unfold evolvedMeasure
  rw [VectorMeasure.map_apply _ hπ ht, withDensityᵥ_apply (integrable_phase_finite _ ph hph hph1)
    (hπ ht), ← integral_indicator (hπ ht)]
  refine integral_snd_compProd μ κ _ ?_
  exact ((integrable_phase_finite _ ph hph hph1).indicator (hπ ht))

/-- **Mass of `|η|`.**  If every fibre has total variation at most `δ`, so does `η` up to `μ(X)`. -/
lemma evolved_variation_le (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (δ : ℝ≥0∞) (hδ : ∀ x, (fibreMeasure κ ph π x).variation univ ≤ δ) :
    (evolvedMeasure μ κ ph π).variation univ ≤ μ univ * δ := by
  refine le_of_forall_lt (fun a ha => ?_)
  obtain ⟨P, hPs, hPd, hPm, hsum⟩ :=
    (evolvedMeasure μ κ ph π).exists_lt_sum_of_lt_variation MeasurableSet.univ ha
  have hfib : ∀ t ∈ P, Measurable (fun x => ‖fibreMeasure κ ph π x t‖ₑ) := by
    intro t ht
    have hm : StronglyMeasurable (fun q : X × Y => (π ⁻¹' t).indicator ph q.2) :=
      ((hph.indicator (hπ (hPm t ht))).comp measurable_snd).stronglyMeasurable
    have h1 : ∀ x, fibreMeasure κ ph π x t = ∫ y, (π ⁻¹' t).indicator ph y ∂κ x :=
      fun x => fibreMeasure_apply κ ph π hph hph1 hπ x (hPm t ht)
    simp_rw [h1]
    exact (hm.integral_kernel_prod_right' (κ := κ)).measurable.enorm
  have hle : ∀ t ∈ P, ‖evolvedMeasure μ κ ph π t‖ₑ ≤ ∫⁻ x, ‖fibreMeasure κ ph π x t‖ₑ ∂μ := by
    intro t ht
    rw [evolvedMeasure_apply μ κ ph π hph hph1 hπ (hPm t ht)]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr (fun x => ?_)
    rw [fibreMeasure_apply κ ph π hph hph1 hπ x (hPm t ht)]
  calc a < ∑ t ∈ P, ‖evolvedMeasure μ κ ph π t‖ₑ := hsum
    _ ≤ ∑ t ∈ P, ∫⁻ x, ‖fibreMeasure κ ph π x t‖ₑ ∂μ := Finset.sum_le_sum hle
    _ = ∫⁻ x, ∑ t ∈ P, ‖fibreMeasure κ ph π x t‖ₑ ∂μ :=
        (lintegral_finsetSum' P (fun t ht => (hfib t ht).aemeasurable)).symm
    _ ≤ ∫⁻ _x, δ ∂μ := by
        refine lintegral_mono (fun x => ?_)
        exact (VectorMeasure.le_variation (fibreMeasure κ ph π x) MeasurableSet.univ hPs hPd).trans
          (hδ x)
    _ = μ univ * δ := by rw [lintegral_const, mul_comm]


/-- The variation measure of `η` is finite. -/
lemma evolved_variation_finite (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    IsFiniteMeasure (evolvedMeasure μ κ ph π).variation := by
  have hle : (evolvedMeasure μ κ ph π).variation ≤ ((μ ⊗ₘ κ).snd).map π := by
    unfold evolvedMeasure
    refine VectorMeasure.variation_map_le.trans ?_
    rw [variation_density_one _ ph hph hph1]
  have : IsFiniteMeasure (((μ ⊗ₘ κ).snd).map π) := inferInstance
  exact isFiniteMeasure_of_le _ hle

end HypoellipticAleksandrov.KineticAleksandrov.Green
