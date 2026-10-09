module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Defs
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The duality identity for the smoothed density

for a finite kernel
`κ` over a base `α` and a nonnegative test function `ψ`,
`∫ ψ ρ_ε = ∫ (Φ̌_ε * ψ) dΓ`, with `Γ = μ ⊗ₘ κ`, `ρ_ε(τ, y) = ∫ Φ_ε(y - y') dκ_τ(y')`, and
`(Φ̌_ε * ψ)(τ, y') = ∫ ψ(τ, y) Φ_ε(y - y') dy`.  The identity is proved with nonnegative
integrals, by Tonelli.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ} {lam : ℝ}

/-- Lebesgue measure on phase space is an additive Haar measure (local instance). -/
local instance absorbVolumeIsAddHaar (d : ℕ) :
    (volume : Measure (EvolutionAmbientState d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The adjoint smoothing `(Φ̌_ε * ψ)(τ, y') = ∫ ψ(τ, y) Φ_ε(y - y') dy` of a test function
`ψ` on the product of a base space and phase space. -/
def dualSmooth {α : Type*} (Φ : SmoothingKernelFamily d lam) (ε : ℝ)
    (ψ : α × EvolutionAmbientState d → ℝ) (x : α × EvolutionAmbientState d) : ℝ :=
  ∫ y, ψ (x.1, y) * Φ.kernel ε (y - x.2)

theorem SmoothingKernelFamily.measurable_sub {Φ : SmoothingKernelFamily d lam} {ε : ℝ}
    (hε : 0 < ε) :
    Measurable fun p : EvolutionAmbientState d × EvolutionAmbientState d =>
      Φ.kernel ε (p.1 - p.2) :=
  (Φ.measurable_kernel hε).comp (measurable_fst.sub measurable_snd)

theorem SmoothingKernelFamily.integrable_sub_right {Φ : SmoothingKernelFamily d lam} {ε : ℝ}
    (hε : 0 < ε) (y' : EvolutionAmbientState d) :
    Integrable (fun y => Φ.kernel ε (y - y')) :=
  (Φ.integrable_kernel hε).comp_sub_right y'

theorem SmoothingKernelFamily.integral_sub_right {Φ : SmoothingKernelFamily d lam} {ε : ℝ}
    (hε : 0 < ε) (y' : EvolutionAmbientState d) :
    ∫ y, Φ.kernel ε (y - y') = 1 := by
  rw [integral_sub_right_eq_self (fun y => Φ.kernel ε y)]
  exact Φ.integral_eq_one hε

/-- The smoothed density of a finite measure as a nonnegative integral. -/
theorem ofReal_smoothDensity {Φ : SmoothingKernelFamily d lam} {ε : ℝ} (hε : 0 < ε)
    (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m] (y : EvolutionAmbientState d) :
    ENNReal.ofReal (smoothDensity Φ ε m y) =
      ∫⁻ y', ENNReal.ofReal (Φ.kernel ε (y - y')) ∂m := by
  unfold smoothDensity
  refine ofReal_integral_eq_lintegral_ofReal ?_
    (Filter.Eventually.of_forall fun y' => (Φ.pos hε _).le)
  refine Integrable.of_bound
    (((Φ.measurable_kernel hε).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Φ.supConst * (ε ^ (2 * d))⁻¹) (Filter.Eventually.of_forall fun y' => ?_)
  rw [Real.norm_of_nonneg (Φ.pos hε _).le]
  exact Φ.le_sup hε _

/-- The adjoint smoothing of a bounded nonnegative function is nonnegative and bounded by the
same constant. -/
theorem dualSmooth_nonneg_le {α : Type*} {Φ : SmoothingKernelFamily d lam} {ε : ℝ}
    (hε : 0 < ε) {ψ : α × EvolutionAmbientState d → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) {B : ℝ}
    (hψB : ∀ x, ψ x ≤ B) (x : α × EvolutionAmbientState d) :
    0 ≤ dualSmooth Φ ε ψ x ∧ dualSmooth Φ ε ψ x ≤ B := by
  have hB : 0 ≤ B := (hψ0 x).trans (hψB x)
  refine ⟨integral_nonneg fun y => mul_nonneg (hψ0 _) (Φ.pos hε _).le, ?_⟩
  calc dualSmooth Φ ε ψ x ≤ ∫ y, B * Φ.kernel ε (y - x.2) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => mul_nonneg (hψ0 _) (Φ.pos hε _).le)
          ((Φ.integrable_sub_right hε x.2).const_mul B)
          (Filter.Eventually.of_forall fun y => ?_)
        exact mul_le_mul_of_nonneg_right (hψB _) (Φ.pos hε _).le
    _ = B := by rw [integral_const_mul, Φ.integral_sub_right hε, mul_one]

theorem integrable_mul_kernel_sub {Φ : SmoothingKernelFamily d lam} {ε : ℝ} (hε : 0 < ε)
    {g : EvolutionAmbientState d → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ y, |g y| ≤ B)
    (y' : EvolutionAmbientState d) :
    Integrable (fun y => g y * Φ.kernel ε (y - y')) :=
  (Φ.integrable_sub_right hε y').bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hgB y)

/-- Tonelli on one slice: pairing a nonnegative function with the smoothed density of a finite
measure equals pairing its adjoint smoothing with the measure. -/
theorem lintegral_mul_smoothDensity_eq {Φ : SmoothingKernelFamily d lam} {ε : ℝ} (hε : 0 < ε)
    (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
    {g : EvolutionAmbientState d → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {B : ℝ}
    (hgB : ∀ y, g y ≤ B) :
    ∫⁻ y, ENNReal.ofReal (g y) * ENNReal.ofReal (smoothDensity Φ ε m y) =
      ∫⁻ y', ENNReal.ofReal (∫ y, g y * Φ.kernel ε (y - y')) ∂m := by
  have hgB' : ∀ y, |g y| ≤ B := fun y => by rw [abs_of_nonneg (hg0 y)]; exact hgB y
  have h1 : ∀ y, ENNReal.ofReal (g y) * ENNReal.ofReal (smoothDensity Φ ε m y) =
      ∫⁻ y', ENNReal.ofReal (g y) * ENNReal.ofReal (Φ.kernel ε (y - y')) ∂m := fun y => by
    rw [ofReal_smoothDensity hε m y, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas : Measurable fun p : EvolutionAmbientState d × EvolutionAmbientState d =>
      ENNReal.ofReal (g p.1) * ENNReal.ofReal (Φ.kernel ε (p.1 - p.2)) :=
    (ENNReal.measurable_ofReal.comp (hg.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (SmoothingKernelFamily.measurable_sub hε))
  simp_rw [h1]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun y' => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_mul_kernel_sub hε hg hgB' y')
    (Filter.Eventually.of_forall fun y => mul_nonneg (hg0 y) (Φ.pos hε _).le)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_mul (hg0 y)]

section Product

variable {α : Type*} [MeasurableSpace α]

/-- The smoothed slice densities are jointly measurable. -/
theorem measurable_ofReal_smoothDensity {Φ : SmoothingKernelFamily d lam} {ε : ℝ} (hε : 0 < ε)
    (κ : Kernel α (EvolutionAmbientState d)) [IsFiniteKernel κ] :
    Measurable fun x : α × EvolutionAmbientState d =>
      ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2) := by
  let κ' : Kernel (α × EvolutionAmbientState d) (EvolutionAmbientState d) :=
    κ.comap Prod.fst measurable_fst
  have h : (fun x : α × EvolutionAmbientState d =>
      ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2)) =
      fun x => ∫⁻ y', ENNReal.ofReal (Φ.kernel ε (x.2 - y')) ∂(κ' x) := by
    funext x
    rw [ofReal_smoothDensity hε (κ x.1) x.2]
    rfl
  rw [h]
  exact Measurable.lintegral_kernel_prod_right'
    (κ := κ')
    (f := fun p : (α × EvolutionAmbientState d) × EvolutionAmbientState d =>
      ENNReal.ofReal (Φ.kernel ε (p.1.2 - p.2)))
    (ENNReal.measurable_ofReal.comp ((Φ.measurable_kernel hε).comp
      ((measurable_snd.comp measurable_fst).sub measurable_snd)))

theorem measurable_dualSmooth {Φ : SmoothingKernelFamily d lam} {ε : ℝ} (hε : 0 < ε)
    {ψ : α × EvolutionAmbientState d → ℝ} (hψ : Measurable ψ) :
    Measurable (dualSmooth Φ ε ψ) := by
  have h : StronglyMeasurable fun p : (α × EvolutionAmbientState d) × EvolutionAmbientState d =>
      ψ (p.1.1, p.2) * Φ.kernel ε (p.2 - p.1.2) :=
    (hψ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((Φ.measurable_kernel hε).comp (measurable_snd.sub (measurable_snd.comp measurable_fst)))
      |>.stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right' h).measurable

/-- **Duality identity**:
`∫ ψ ρ_ε = ∫ (Φ̌_ε * ψ) dΓ` for `Γ = μ ⊗ₘ κ`, `ρ_ε(τ, y) = ∫ Φ_ε(y - y') dκ_τ(y')`. -/
theorem lintegral_mul_smoothDensity_prod_eq {Φ : SmoothingKernelFamily d lam} {ε : ℝ}
    (hε : 0 < ε) (μ : Measure α) [SFinite μ] (κ : Kernel α (EvolutionAmbientState d))
    [IsFiniteKernel κ] {ψ : α × EvolutionAmbientState d → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {B : ℝ} (hψB : ∀ x, ψ x ≤ B) :
    ∫⁻ x, ENNReal.ofReal (ψ x) * ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2)
        ∂(μ.prod volume) =
      ∫⁻ x, ENNReal.ofReal (dualSmooth Φ ε ψ x) ∂(μ ⊗ₘ κ) := by
  have hm : Measurable fun x : α × EvolutionAmbientState d =>
      ENNReal.ofReal (ψ x) * ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2) :=
    (ENNReal.measurable_ofReal.comp hψ).mul (measurable_ofReal_smoothDensity hε κ)
  rw [lintegral_prod _ hm.aemeasurable, Measure.lintegral_compProd
    (f := fun x => ENNReal.ofReal (dualSmooth Φ ε ψ x))
    (ENNReal.measurable_ofReal.comp (measurable_dualSmooth hε hψ))]
  refine lintegral_congr fun τ => ?_
  have := lintegral_mul_smoothDensity_eq (Φ := Φ) hε (κ τ)
    (g := fun y => ψ (τ, y)) (hψ.comp measurable_prodMk_left) (fun y => hψ0 _) (B := B)
    (fun y => hψB _)
  exact this

end Product

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
