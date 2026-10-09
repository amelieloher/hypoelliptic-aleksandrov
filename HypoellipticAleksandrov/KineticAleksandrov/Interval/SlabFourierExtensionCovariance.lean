module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionComposition

/-! # Position-translation covariance of the zero extension

Position translation does not alter interval membership of velocity. Thus it
commutes with inclusion and preserves both interior and zero exterior fibers.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Inclusion of interval states commutes with position translation. -/
theorem intervalStateInclusion_shift {a c : ℝ} (σ : ℝ) (z : PDE.Vec 1)
    (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ) :
    evolutionStateShift (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ z
      (intervalStateInclusion σ p) =
      intervalStateInclusion σ
        (evolutionStateShift (PDE.oneDimensionalAxisBox a c) stationary σ z p) := rfl

/-- Literal zero extension preserves position-translation covariance. -/
theorem intervalExtension_covariance {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hc : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c)
      stationary hJ K) :
    IsTranslationCovariantEvolution (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      intervalWholeSpace_measurable (intervalExtension hJ K) := by
  intro σ τ hστ z p
  by_cases hp : p.1.1 ∈ PDE.oneDimensionalAxisBox a c
  · let pj : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
      ⟨p.1, by simpa only [evolutionStateSet, mem_prod, movingDomain_stationary,
        mem_univ, and_true] using hp⟩
    have he : intervalStateInclusion σ pj = p := Subtype.ext rfl
    rw [← he, intervalStateInclusion_shift, intervalExtension_fiber_inside,
      intervalExtension_fiber_inside,
      Measure.map_map (measurable_evolutionStateShift _ _ τ z)
        (measurable_intervalStateInclusion τ),
      ← hc σ τ hστ z pj,
      Measure.map_map (measurable_intervalStateInclusion τ)
        (measurable_evolutionStateShift _ _ τ z)]
    rfl
  · have hs : (evolutionStateShift (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ z p).1.1
        ∉ PDE.oneDimensionalAxisBox a c := hp
    rw [intervalExtension_fiber_outside hJ K σ τ hστ p hp,
      intervalExtension_fiber_outside hJ K σ τ hστ _ hs, Measure.map_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
