module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Continued measures by kernel integration

For a measure `R` on the fixed-time moving fiber `EvolutionState Ω γ s` and a moving-fiber
kernel `K`, the *continued measure* `E` is the ambient measure
`E A = ∫⁻ p, K.master (query s T p) A ∂R` (the killed continuation of `R` from time `s` to
time `T`).  It is characterised by these set integrals on measurable sets alone: this module
proves existence and uniqueness of such an `E` (`exists_unique_continuedMeasure`) without any
integrability, measurability or composition premise beyond the bundled Borel kernel, and
records the elementary mass, support, additivity and domination facts consumed by the
domination and trimming steps.

The integrand query is `evolutionQueryOfState Ω γ s T hsT p`, which unfolds to the source
`movingQuery s T hsT p.1.1 p.1.2 p.2.1` (`evolutionQueryOfState_eq`).
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The canonical valid query of a fiber state is the explicit source query
`(s, T, v, z)` with `v` in the moving domain. -/
theorem evolutionQueryOfState_eq (s T : ℝ) (hsT : s ≤ T) (p : EvolutionState Ω γ s) :
    evolutionQueryOfState Ω γ s T hsT p =
      ⟨(s, T, p.1.1, p.1.2), hsT, p.2.1, Set.mem_univ _⟩ := rfl

/-- The kernel from fiber states at time `s` to ambient states: run the master kernel from
`s` to `T`. -/
noncomputable def continuationKernel (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T) :
    ProbabilityTheory.Kernel (EvolutionState Ω γ s) (EvolutionAmbientState d) :=
  ProbabilityTheory.Kernel.comap K.master (evolutionQueryOfState Ω γ s T hsT)
    (measurable_evolutionQueryOfState Ω γ s T hsT)

/-- The continuation kernel evaluated at a fiber state is the master measure of its query. -/
theorem continuationKernel_apply (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (p : EvolutionState Ω γ s) :
    continuationKernel K hsT p = K.master (evolutionQueryOfState Ω γ s T hsT p) := rfl

/-- The continued measure of `R`: the integral of the continuation kernel against `R`. -/
noncomputable def continuedMeasure (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s)) : Measure (EvolutionAmbientState d) :=
  R.bind (continuationKernel K hsT)

/-- Set-integral formula for the continued measure on measurable sets. -/
theorem continuedMeasure_apply (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s)) {A : Set (EvolutionAmbientState d)}
    (hA : MeasurableSet A) :
    continuedMeasure K hsT R A =
      ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) A ∂R :=
  Measure.bind_apply hA (continuationKernel K hsT).measurable.aemeasurable

/-- Existence and uniqueness of the continued measure with the literal source set integrals.
Only the bundled Borel master kernel is used; `R` need not even be finite. -/
theorem exists_unique_continuedMeasure (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s)) :
    ∃! E : Measure (EvolutionAmbientState d), ∀ A : Set (EvolutionAmbientState d),
      MeasurableSet A →
        E A = ∫⁻ p, K.master ⟨(s, T, p.1.1, p.1.2), hsT, p.2.1, Set.mem_univ _⟩ A ∂R := by
  refine ⟨continuedMeasure K hsT R, fun A hA => continuedMeasure_apply K hsT R hA, ?_⟩
  intro E hE
  refine Measure.ext fun A hA => ?_
  rw [hE A hA]
  exact (continuedMeasure_apply K hsT R hA).symm

/-- Any measure with the displayed set integrals is the continued measure. -/
theorem eq_continuedMeasure_of_apply (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s)) {E : Measure (EvolutionAmbientState d)}
    (hE : ∀ A : Set (EvolutionAmbientState d), MeasurableSet A →
      E A = ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) A ∂R) :
    E = continuedMeasure K hsT R :=
  Measure.ext fun A hA => (hE A hA).trans (continuedMeasure_apply K hsT R hA).symm

/-- The continued measure has at most the mass of the initial measure. -/
theorem continuedMeasure_univ_le (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s)) :
    continuedMeasure K hsT R Set.univ ≤ R Set.univ := by
  rw [continuedMeasure_apply K hsT R MeasurableSet.univ]
  calc ∫⁻ p, K.master (evolutionQueryOfState Ω γ s T hsT p) Set.univ ∂R
      ≤ ∫⁻ _p, 1 ∂R := lintegral_mono fun p => K.mass_le_one _
    _ = R Set.univ := by simp

/-- The continued measure of a finite measure is finite. -/
instance isFiniteMeasure_continuedMeasure (K : MovingFiberKernel Ω γ) {s T : ℝ}
    (hsT : s ≤ T) (R : Measure (EvolutionState Ω γ s)) [IsFiniteMeasure R] :
    IsFiniteMeasure (continuedMeasure K hsT R) :=
  ⟨(continuedMeasure_univ_le K hsT R).trans_lt (measure_lt_top R _)⟩

/-- The continued measure gives no mass outside the terminal state fiber. -/
theorem continuedMeasure_terminal_support (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    {s T : ℝ} (hsT : s ≤ T) (R : Measure (EvolutionState Ω γ s)) :
    continuedMeasure K hsT R (evolutionStateSet Ω γ T)ᶜ = 0 := by
  have hS : MeasurableSet (evolutionStateSet Ω γ T) := measurableSet_evolutionStateSet hΩ T
  rw [continuedMeasure_apply K hsT R hS.compl]
  have hz : ∀ p : EvolutionState Ω γ s,
      K.master (evolutionQueryOfState Ω γ s T hsT p) (evolutionStateSet Ω γ T)ᶜ = 0 := by
    intro p
    have h : (K.master (evolutionQueryOfState Ω γ s T hsT p)).restrict
        (evolutionStateSet Ω γ T) = K.master (evolutionQueryOfState Ω γ s T hsT p) :=
      K.terminal_support (evolutionQueryOfState Ω γ s T hsT p)
    calc K.master (evolutionQueryOfState Ω γ s T hsT p) (evolutionStateSet Ω γ T)ᶜ
        = ((K.master (evolutionQueryOfState Ω γ s T hsT p)).restrict
            (evolutionStateSet Ω γ T)) (evolutionStateSet Ω γ T)ᶜ := by
          rw [h]
      _ = 0 := by rw [Measure.restrict_apply hS.compl, compl_inter_self, measure_empty]
  simp [hz]

/-- Continuation is additive in the initial measure. -/
theorem continuedMeasure_add (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R₁ R₂ : Measure (EvolutionState Ω γ s)) :
    continuedMeasure K hsT (R₁ + R₂) =
      continuedMeasure K hsT R₁ + continuedMeasure K hsT R₂ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.add_apply, continuedMeasure_apply K hsT _ hA,
    continuedMeasure_apply K hsT _ hA, continuedMeasure_apply K hsT _ hA,
    lintegral_add_measure]

/-- Continuation is monotone in the initial measure. -/
theorem continuedMeasure_mono (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    {R R' : Measure (EvolutionState Ω γ s)} (h : R ≤ R') :
    continuedMeasure K hsT R ≤ continuedMeasure K hsT R' := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [continuedMeasure_apply K hsT _ hA, continuedMeasure_apply K hsT _ hA]
  exact lintegral_mono' h le_rfl

/-- Pointwise domination of the continuation kernel by another kernel gives domination of the
continued measure by the integral of that kernel. -/
theorem continuedMeasure_le_bind (K : MovingFiberKernel Ω γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState Ω γ s))
    (κ : ProbabilityTheory.Kernel (EvolutionState Ω γ s) (EvolutionAmbientState d))
    (h : ∀ p, K.master (evolutionQueryOfState Ω γ s T hsT p) ≤ κ p) :
    continuedMeasure K hsT R ≤ R.bind κ := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [continuedMeasure_apply K hsT _ hA, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact lintegral_mono fun p => h p A

end HypoellipticAleksandrov.KineticAleksandrov.Decay
