module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityFubini
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SliceBounds
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Green
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Slices

/-!
# The time-mollified Green density as a convolution of the slice densities

the smoothed density
`ρ^δ_ε(τ, y) = ∫ η_δ(τ - s) (ν_s)_ε(y) ds` of the Green measure is the time convolution of the
slice densities `(ν_s)_ε(y)`, extended by zero outside the elapsed-time carrier.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam : ℝ}

instance isFiniteMeasure_sliceMeasure {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞}
    (τ : ElapsedTime S) : IsFiniteMeasure (sliceMeasure K σ₀ p τ) :=
  ⟨lt_of_le_of_lt (sliceMeasure_univ_le_one K σ₀ p τ) ENNReal.one_lt_top⟩

theorem sliceMeasure_real_univ_le {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞}
    (τ : ElapsedTime S) : (sliceMeasure K σ₀ p τ).real Set.univ ≤ 1 := by
  rw [Measure.real, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (sliceMeasure_univ_le_one K σ₀ p τ)

variable {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The slice density `τ ↦ (ν_τ)_ε(y)`, extended by zero off the elapsed-time carrier. -/
def greenSliceFun (hl : 0 < lam) (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} (ε : ℝ) (y : EvolutionAmbientState d) : ℝ → ℝ :=
  Function.extend Subtype.val
    (fun a : ElapsedTime S => smoothDensity (flowKernelFamily (d := d) hl) ε
      (sliceMeasure K σ₀ p a) y) 0

theorem greenSliceFun_apply (hl : 0 < lam) (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} (ε : ℝ) (y : EvolutionAmbientState d)
    (a : ElapsedTime S) :
    greenSliceFun hl K σ₀ p (S := S) ε y a.1 = smoothDensity (flowKernelFamily (d := d) hl) ε
      (sliceMeasure K σ₀ p a) y :=
  Subtype.val_injective.extend_apply _ _ a

theorem greenSliceFun_apply_of_not (hl : 0 < lam) (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} (ε : ℝ) (y : EvolutionAmbientState d) {s : ℝ}
    (hs : ¬ (0 < s ∧ ENNReal.ofReal s < S)) :
    greenSliceFun hl K σ₀ p (S := S) ε y s = 0 := by
  unfold greenSliceFun
  rw [Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hs (ha ▸ a.2))]
  rfl

theorem measurable_greenSliceFun (hl : 0 < lam) (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε) (y : EvolutionAmbientState d) :
    Measurable (greenSliceFun hl K σ₀ p (S := S) ε y) := by
  refine (MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime S)).measurable_extend ?_
    measurable_const
  have h1 := measurable_ofReal_smoothDensity (Φ := flowKernelFamily (d := d) hl) hε
    (sliceKernel K σ₀ p S)
  have h2 : Measurable fun a : ElapsedTime S => ENNReal.ofReal
      (smoothDensity (flowKernelFamily (d := d) hl) ε (sliceKernel K σ₀ p S a) y) :=
    h1.comp (measurable_id.prodMk measurable_const)
  have h3 := h2.ennreal_toReal
  have e : (fun a : ElapsedTime S => smoothDensity (flowKernelFamily (d := d) hl) ε
      (sliceMeasure K σ₀ p a) y) = fun a => (ENNReal.ofReal
      (smoothDensity (flowKernelFamily (d := d) hl) ε (sliceKernel K σ₀ p S a) y)).toReal :=
    funext fun a => (ENNReal.toReal_ofReal (smoothDensity_nonneg _ _ hε y)).symm
  rw [e]
  exact h3

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
