module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Integration against a modulus-one complex density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal

/-- A modulus-one density has precisely the original positive variation measure. -/
theorem variation_density_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (g : α → ℂ) (hg : Measurable g) (hn : ∀ x, ‖g x‖ = 1) :
    (μ.withDensityᵥ g).variation = μ := by
  have hi : Integrable g μ := Integrable.mono' (integrable_const (1 : ℝ))
    hg.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => (hn x).le))
  rw [Measure.variation_withDensityᵥ hi]
  have he : (fun x => ‖g x‖ₑ) = 1 := by
    funext x
    rw [← ofReal_norm, hn x]
    norm_num
  rw [he, withDensity_one]

/-- Complex integration against a modulus-one density is ordinary weighted integration. -/
theorem integral_density_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (g : α → ℂ) (hg : Measurable g) (hn : ∀ x, ‖g x‖ = 1)
    (f : α → ℂ) (hf : Integrable f μ) :
    (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ g]) =
      ∫ x, f x * g x ∂μ := by
  let ν := μ.withDensityᵥ g
  have hv : ν.variation = μ := variation_density_one μ g hg hn
  have : IsFiniteMeasure ν.variation := by rw [hv]; infer_instance
  have hgi : Integrable g μ := Integrable.mono' (integrable_const (1 : ℝ))
    hg.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => (hn x).le))
  have hm : ∀ f : α → ℂ, Integrable f μ → Integrable (fun x => f x * g x) μ :=
    fun f hf => hf.mul_bdd hg.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => (hn x).le))
  let J : (α →₁[μ] ℂ) →ₗ[ℝ] ℂ :=
    { toFun := fun u => ∫ x, u x * g x ∂μ
      map_add' := fun u v => by
        rw [← integral_add (hm u (L1.integrable_coeFn u)) (hm v (L1.integrable_coeFn v))]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add u v] with x hx
        simp only [hx, Pi.add_apply, add_mul]
      map_smul' := fun c u => by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c u] with x hx
        simp only [hx, Pi.smul_apply, smul_mul_assoc, RingHom.id_apply] }
  have hJ : ∀ u, ‖J u‖ ≤ 1 * ‖u‖ := by
    intro u
    change ‖∫ x, u x * g x ∂μ‖ ≤ 1 * ‖u‖
    calc
      _ ≤ ∫ x, ‖u x * g x‖ ∂μ := norm_integral_le_integral_norm _
      _ = 1 * ‖u‖ := by
        simp only [norm_mul, hn, mul_one, one_mul, L1.norm_eq_integral_norm]
  have hc := (J.mkContinuous 1 hJ).continuous
  apply hf.induction (P := fun f =>
    (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) = ∫ x, f x * g x ∂μ)
  · intro c E hE hfinite
    rw [VectorMeasure.integral_indicator_const c hE, withDensityᵥ_apply hgi hE]
    change c * (∫ x in E, g x ∂μ) = ∫ x, E.indicator (fun _ => c) x * g x ∂μ
    rw [← integral_const_mul]
    have he : (fun x => E.indicator (fun _ => c) x * g x) =
        E.indicator (fun x => c * g x) := by
      funext x
      by_cases hx : x ∈ E <;> simp only [Set.indicator, hx, ↓reduceIte, zero_mul]
    rw [he, integral_indicator hE]
  · intro f₁ f₂ hd h₁ h₂ he₁ he₂
    have hi₁ : ν.Integrable f₁ := by simpa only [VectorMeasure.Integrable, hv] using h₁
    have hi₂ : ν.Integrable f₂ := by simpa only [VectorMeasure.Integrable, hv] using h₂
    rw [VectorMeasure.integral_add hi₁ hi₂, he₁, he₂, ← integral_add (hm f₁ h₁) (hm f₂ h₂)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => (add_mul (f₁ x) (f₂ x) (g x)).symm)
  · apply isClosed_eq _ hc
    have hcv := VectorMeasure.continuous_integral (μ := ν)
      (B := ContinuousLinearMap.mul ℝ ℂ)
    rw [hv] at hcv
    exact hcv
  · intro f₁ f₂ he hi hp
    have heν : f₁ =ᵐ[ν.variation] f₂ := by simpa only [hv] using he
    rw [← VectorMeasure.integral_congr_ae heν, hp]
    apply integral_congr_ae
    exact he.mono (fun x hx => congrArg (fun z => z * g x) hx)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
