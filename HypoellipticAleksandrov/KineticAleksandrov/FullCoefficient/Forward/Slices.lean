module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green

/-!
# The slice description of the Green measure of a point mass

The slice description: the Green measure `Γ` of a point mass `δ_p` at the pole time `σ₀` is
`Γ = ∫ dτ δ_τ ⊗ ν_τ` with the slice `ν_τ = K.master (elapsedQuery σ₀ p τ)`.  Each slice has mass
at most one, and `τ ↦ ν_τ(E)` is Borel for every Borel `E`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The slice `ν_τ` of the Green measure of a point mass at `p`, at elapsed time `τ`. -/
def sliceMeasure (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀)
    {S : ℝ≥0∞} (τ : ElapsedTime S) : Measure (EvolutionAmbientState d) :=
  K.master (elapsedQuery σ₀ p τ)

/-- Every slice has mass at most one. -/
theorem sliceMeasure_univ_le_one (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} (τ : ElapsedTime S) :
    sliceMeasure K σ₀ p τ Set.univ ≤ 1 :=
  K.mass_le_one _

/-- The elapsed-time query of a fixed pole is measurable in the elapsed time. -/
theorem measurable_elapsedQuery_left (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀) (S : ℝ≥0∞) :
    Measurable (fun τ : ElapsedTime S => elapsedQuery σ₀ p τ) := by
  apply Measurable.subtype_mk
  change Measurable (fun τ : ElapsedTime S => (σ₀, (σ₀ + τ.1, p.1)))
  fun_prop

/-- The slice masses of Borel sets are Borel in the elapsed time. -/
theorem measurable_sliceMeasure_apply (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) (S : ℝ≥0∞) {E : Set (EvolutionAmbientState d)}
    (hE : MeasurableSet E) :
    Measurable (fun τ : ElapsedTime S => sliceMeasure K σ₀ p τ E) :=
  (K.master.measurable_coe hE).comp (measurable_elapsedQuery_left σ₀ p S)

/-- The slice kernel `τ ↦ ν_τ`. -/
def sliceKernel (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀)
    (S : ℝ≥0∞) : Kernel (ElapsedTime S) (EvolutionAmbientState d) :=
  K.master.comap (fun τ : ElapsedTime S => elapsedQuery σ₀ p τ)
    (measurable_elapsedQuery_left σ₀ p S)

theorem sliceKernel_apply (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀)
    (S : ℝ≥0∞) (τ : ElapsedTime S) : sliceKernel K σ₀ p S τ = sliceMeasure K σ₀ p τ :=
  rfl

instance sliceKernel_isFiniteKernel (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) (S : ℝ≥0∞) : IsFiniteKernel (sliceKernel K σ₀ p S) := by
  unfold sliceKernel
  infer_instance

/-- **Slice description**: the Green measure of a point mass is the
disintegration `Γ = ∫ dτ δ_τ ⊗ ν_τ` along the elapsed time. -/
theorem green_eq_compProd (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (p : EvolutionState Ω γ σ₀)
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ S (Measure.dirac p) Γ) :
    Γ = elapsedVolume S ⊗ₘ sliceKernel K σ₀ p S := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [hΓ F hF, lintegral_dirac, Measure.lintegral_compProd hF]
  rfl

/-- The Green measure of a point mass in iterated-integral form. -/
theorem lintegral_green_eq (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (p : EvolutionState Ω γ σ₀)
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ S (Measure.dirac p) Γ)
    (F : ElapsedTime S × EvolutionAmbientState d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ q, F q ∂Γ = ∫⁻ τ, ∫⁻ w, F (τ, w) ∂sliceMeasure K σ₀ p τ ∂elapsedVolume S := by
  rw [green_eq_compProd K σ₀ S p Γ hΓ, Measure.lintegral_compProd hF]
  rfl

/-- The time marginal of the Green measure of a point mass is at most the elapsed Lebesgue
measure: every slice has mass at most one. -/
theorem green_prod_fst_le (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (p : EvolutionState Ω γ σ₀)
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ S (Measure.dirac p) Γ) (A : Set (ElapsedTime S))
    (hA : MeasurableSet A) : Γ (Prod.fst ⁻¹' A) ≤ elapsedVolume S A := by
  have := greenMeasure_timeMarginal_le K σ₀ S (Measure.dirac p) Γ hΓ A hA
  simpa using this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
