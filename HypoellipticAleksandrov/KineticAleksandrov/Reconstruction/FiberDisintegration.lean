module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.VecFourierInversion
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Disintegration and jointly measurable Fourier representatives

Step Lemma 5.2 of the reconstruction lemma.  A finite measure
`Γ` on `Y × ℝ^d` whose `Y`-marginal is `g dm` disintegrates as
`Γ(dy dz) = g(y) π_y(dz) m(dy)` with probability kernel `π = Γ.condKernel`.  The representatives
`k̃^ξ(y) = g(y) ∫ e^{-i ξ·z} π_y(dz)` of the Fourier-marginal densities are jointly measurable in
`(ξ, y)` and continuous in `ξ`; for every `ξ` they agree `m`-almost everywhere with the
hypothesised density `k^ξ`, so all `L^p` norms and the constant `𝖧` are unchanged; and the height
`H(y) = (2π)^{-d} ∫ |k̃^ξ(y)| dξ` is measurable.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The Fourier transform `ξ ↦ ∫ e^{-i ξ·z} π_y(dz)` of the fibre measure `κ y`. -/
def fiberFourier (κ : Kernel Y (PDE.Vec d)) (ξ : PDE.Vec d) (y : Y) : ℂ :=
  ∫ z, cexp (-((PDE.vecDot ξ z : ℝ) * I)) ∂(κ y)

/-- The fibre representative `k̃^ξ(y) = g(y) ∫ e^{-i ξ·z} π_y(dz)` of the Fourier-marginal
density. -/
def fiberDensity (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (ξ : PDE.Vec d) (y : Y) : ℂ :=
  ((g y).toReal : ℂ) * fiberFourier κ ξ y

/-- The fibre height `H(y) = (2π)^{-d} ∫ |k̃^ξ(y)| dξ`. -/
def fiberHeight (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (y : Y) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) * ∫⁻ ξ, ‖fiberDensity g κ ξ y‖ₑ

/-- The character `ξ ↦ e^{-i ξ·z}` is continuous. -/
lemma continuous_exp_vecDot (z : PDE.Vec d) :
    Continuous fun ξ : PDE.Vec d => cexp (-((PDE.vecDot ξ z : ℝ) * I)) := by
  unfold PDE.vecDot
  fun_prop

/-- The character `e^{-i ξ·z}` has modulus one. -/
lemma norm_exp_vecDot (ξ z : PDE.Vec d) : ‖cexp (-((PDE.vecDot ξ z : ℝ) * I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The fibre Fourier transform is jointly measurable in `(ξ, y)`. -/
lemma measurable_fiberFourier (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] :
    Measurable fun p : PDE.Vec d × Y => fiberFourier κ p.1 p.2 := by
  have hc : Continuous fun q : PDE.Vec d × PDE.Vec d =>
      cexp (-((PDE.vecDot q.1 q.2 : ℝ) * I)) := by
    unfold PDE.vecDot
    fun_prop
  have hf : Measurable fun q : (PDE.Vec d × Y) × PDE.Vec d =>
      cexp (-((PDE.vecDot q.1.1 q.2 : ℝ) * I)) :=
    hc.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have := (hf.stronglyMeasurable).integral_kernel_prod_right'
    (κ := Kernel.prodMkLeft (PDE.Vec d) κ)
  exact this.measurable

/-- The fibre Fourier transform is measurable in `y` for fixed `ξ`. -/
lemma measurable_fiberFourier_right (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ]
    (ξ : PDE.Vec d) : Measurable (fiberFourier κ ξ) :=
  (measurable_fiberFourier κ).comp measurable_prodMk_left

/-- The fibre Fourier transform is continuous in `ξ` for fixed `y`. -/
lemma continuous_fiberFourier (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (y : Y) :
    Continuous fun ξ => fiberFourier κ ξ y := by
  unfold fiberFourier
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_)
    (fun ξ => Filter.Eventually.of_forall fun z => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun z => continuous_exp_vecDot z)
  · exact (Continuous.aestronglyMeasurable (by unfold PDE.vecDot; fun_prop))
  · exact (norm_exp_vecDot ξ z).le

/-- The fibre Fourier transform of a probability kernel is bounded by one. -/
lemma norm_fiberFourier_le (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (ξ : PDE.Vec d)
    (y : Y) : ‖fiberFourier κ ξ y‖ ≤ 1 := by
  unfold fiberFourier
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun z =>
    (norm_exp_vecDot ξ z).le)).trans ?_
  simp


/-- The fibre representatives are jointly measurable in `(ξ, y)`. -/
lemma measurable_fiberDensity {g : Y → ℝ≥0∞} (hg : Measurable g) (κ : Kernel Y (PDE.Vec d))
    [IsSFiniteKernel κ] :
    Measurable fun p : PDE.Vec d × Y => fiberDensity g κ p.1 p.2 :=
  (Complex.measurable_ofReal.comp (hg.comp measurable_snd).ennreal_toReal).mul
    (measurable_fiberFourier κ)

/-- The fibre representative is measurable in `y` for fixed `ξ`. -/
lemma measurable_fiberDensity_right {g : Y → ℝ≥0∞} (hg : Measurable g)
    (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] (ξ : PDE.Vec d) :
    Measurable (fiberDensity g κ ξ) :=
  (measurable_fiberDensity hg κ).comp measurable_prodMk_left

/-- The fibre representative is bounded by `g(y)`. -/
lemma norm_fiberDensity_le {g : Y → ℝ≥0∞} (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ]
    (ξ : PDE.Vec d) (y : Y) : ‖fiberDensity g κ ξ y‖ ≤ (g y).toReal := by
  unfold fiberDensity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (norm_fiberFourier_le κ ξ y)

/-- The fibre height is measurable. -/
lemma measurable_fiberHeight {g : Y → ℝ≥0∞} (hg : Measurable g) (κ : Kernel Y (PDE.Vec d))
    [IsSFiniteKernel κ] : Measurable (fiberHeight g κ) := by
  unfold fiberHeight
  refine Measurable.const_mul ?_ _
  have : Measurable fun q : Y × PDE.Vec d => ‖fiberDensity g κ q.2 q.1‖ₑ :=
    ((measurable_fiberDensity hg κ).comp measurable_swap).enorm
  exact this.lintegral_prod_right'

/-- The Fourier marginal of `(m.withDensity g) ⊗ₘ κ` over `E × ℝ^d` is the integral of the
representative `k̃^ξ` over `E`. -/
lemma setIntegral_fiberDensity {m : Measure Y} {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hgtop : ∀ᵐ y ∂m, g y < ∞) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ]
    [IsFiniteMeasure ((m.withDensity g) ⊗ₘ κ)] [SFinite m] (ξ : PDE.Vec d) {E : Set Y}
    (hE : MeasurableSet E) :
    ∫ y in E, fiberDensity g κ ξ y ∂m =
      ∫ p in E ×ˢ (univ : Set (PDE.Vec d)), cexp (-((PDE.vecDot ξ p.2 : ℝ) * I))
        ∂((m.withDensity g) ⊗ₘ κ) := by
  have hf : Measurable fun p : Y × PDE.Vec d => cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) := by
    have hc : Continuous fun z : PDE.Vec d => cexp (-((PDE.vecDot ξ z : ℝ) * I)) := by
      unfold PDE.vecDot
      fun_prop
    exact hc.measurable.comp measurable_snd
  have hint : IntegrableOn (fun p : Y × PDE.Vec d => cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)))
      (E ×ˢ (univ : Set (PDE.Vec d))) ((m.withDensity g) ⊗ₘ κ) :=
    (Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => (norm_exp_vecDot ξ p.2).le)).integrableOn
  rw [Measure.setIntegral_compProd hE MeasurableSet.univ hint]
  simp only [Measure.restrict_univ]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hg
    (ae_restrict_of_ae hgtop) _ hE]
  refine setIntegral_congr_fun hE fun y _ => ?_
  simp only [fiberDensity, fiberFourier, Complex.real_smul]


/-- The density `g` of the marginal of a finite measure has finite integral. -/
lemma lintegral_ne_top_of_fst_eq {m : Measure Y} {g : Y → ℝ≥0∞}
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] (hΓ : Γ.fst = m.withDensity g) :
    ∫⁻ y, g y ∂m ≠ ∞ := by
  have h : (m.withDensity g) univ = Γ.fst univ := by rw [hΓ]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]
  exact measure_ne_top _ _

/-- The fibre representatives are integrable. -/
lemma integrable_fiberDensity {m : Measure Y} {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hg1 : ∫⁻ y, g y ∂m ≠ ∞) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (ξ : PDE.Vec d) :
    Integrable (fiberDensity g κ ξ) m :=
  (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hg1).mono'
    (measurable_fiberDensity_right hg κ ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg] using norm_fiberDensity_le κ ξ y)

/-- **Step Lemma 5.2.**  Let `Γ` be a finite measure on
`Y × ℝ^d` with `Y`-marginal `g dm`, and suppose that for each `ξ` the measure
`E ↦ ∫_{E × ℝ^d} e^{-i ξ·z} dΓ` has density `k ξ` with respect to `m`.  Then
`Γ = (g dm) ⊗ π` for the probability kernel `π = Γ.condKernel`; the representatives
`k̃^ξ(y) = g(y) ∫ e^{-i ξ·z} π_y(dz)` are jointly measurable in `(ξ, y)`, continuous in `ξ`, and
for each `ξ` equal `k ξ` `m`-almost everywhere, so every `L^p` norm of `k ξ` and the integral of
the `L^γ` norms are unchanged; the height `H` is measurable. -/
theorem fiber_disintegration {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ) :
    Γ = (m.withDensity g) ⊗ₘ Γ.condKernel ∧
    (∀ y, IsProbabilityMeasure (Γ.condKernel y)) ∧
    Measurable (fun p : PDE.Vec d × Y => fiberDensity g Γ.condKernel p.1 p.2) ∧
    (∀ y, Continuous fun ξ => fiberDensity g Γ.condKernel ξ y) ∧
    (∀ ξ, fiberDensity g Γ.condKernel ξ =ᵐ[m] k ξ) ∧
    (∀ ξ (p : ℝ≥0∞), eLpNorm (fiberDensity g Γ.condKernel ξ) p m = eLpNorm (k ξ) p m) ∧
    (∀ p : ℝ≥0∞, ∫⁻ ξ, eLpNorm (fiberDensity g Γ.condKernel ξ) p m =
      ∫⁻ ξ, eLpNorm (k ξ) p m) ∧
    Measurable (fiberHeight g Γ.condKernel) := by
  have hdis : Γ = (m.withDensity g) ⊗ₘ Γ.condKernel := by
    rw [← hΓ]; exact (Measure.disintegrate Γ Γ.condKernel).symm
  have hg1 := lintegral_ne_top_of_fst_eq Γ hΓ
  have hgtop : ∀ᵐ y ∂m, g y < ∞ := ae_lt_top hg hg1
  have hae : ∀ ξ, fiberDensity g Γ.condKernel ξ =ᵐ[m] k ξ := by
    intro ξ
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => (integrable_fiberDensity hg hg1 _ ξ).integrableOn)
      (fun s _ _ => (hk ξ).1.integrableOn) fun s hs _ => ?_
    have : IsFiniteMeasure ((m.withDensity g) ⊗ₘ Γ.condKernel) := by rw [← hdis]; infer_instance
    rw [setIntegral_fiberDensity hg hgtop _ ξ hs, (hk ξ).2 s hs, ← hdis]
  refine ⟨hdis, fun y => inferInstance, measurable_fiberDensity hg _,
    fun y => continuous_const.mul (continuous_fiberFourier _ y), hae,
    fun ξ p => eLpNorm_congr_ae (hae ξ), fun p => ?_, measurable_fiberHeight hg _⟩
  exact lintegral_congr fun ξ => eLpNorm_congr_ae (hae ξ)

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
