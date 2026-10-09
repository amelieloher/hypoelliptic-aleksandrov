module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionFibers

/-! # Chapman–Kolmogorov for the literal zero extension

No endpoint identity is asserted for exterior starts. Composition is preserved
because every nonzero intermediate transition stays inside the interval.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped ProbabilityTheory

/-- Zero extension preserves the composition law of the interval kernel. -/
theorem intervalExtension_composition {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hcomp : K.HasComposition hJ) :
    (intervalExtension hJ K).HasComposition intervalWholeSpace_measurable := by
  intro σ r τ hσr hrτ
  apply ProbabilityTheory.Kernel.ext
  intro p
  apply Measure.ext
  intro A hA
  by_cases hp : p.1.1 ∈ PDE.oneDimensionalAxisBox a c
  · let pj : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
      ⟨p.1, by simpa only [evolutionStateSet, mem_prod, movingDomain_stationary,
        mem_univ, and_true] using hp⟩
    have he : intervalStateInclusion σ pj = p := Subtype.ext rfl
    rw [← he, intervalExtension_fiber_inside,
      Measure.map_apply (measurable_intervalStateInclusion τ) hA,
      hcomp σ r τ hσr hrτ,
      ProbabilityTheory.Kernel.comp_apply' _ _ _
        (hA.preimage (measurable_intervalStateInclusion τ)),
      ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
      intervalExtension_fiber_inside,
      lintegral_map
        (((intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable r τ
          hrτ).measurable_coe hA)
        (measurable_intervalStateInclusion r)]
    apply lintegral_congr_ae
    refine Filter.Eventually.of_forall fun w => ?_
    dsimp only
    rw [intervalExtension_fiber_inside,
      Measure.map_apply (measurable_intervalStateInclusion τ) hA]
  · rw [intervalExtension_fiber_outside hJ K σ τ (hσr.trans hrτ) p hp,
      ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
      intervalExtension_fiber_outside hJ K σ r hσr p hp]
    simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero_measure]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
