module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels

/-! # Interval Fourier measure support and domination by the parabolic marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The ambient velocity marginal is exactly the derived scalar parabolic measure. -/
theorem interval_firstMarginal_eq_parabolic {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    K.firstMarginal (movingQuery σ τ hστ v z hv) =
      P K hJ (scalarQuery σ τ hστ v hv) := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hJ σ τ hστ
    (evolutionStateOfPosition (PDE.oneDimensionalAxisBox a c) stationary σ ⟨v, hv⟩ z)
  rw [← hfirst σ τ hστ ⟨v, hv⟩ z] at hmap
  exact hmap.symm

/-- Fourier variation is dominated on every Borel set by the scalar marginal. -/
theorem intervalFourierKernel_variation_le_parabolic {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) :
    (intervalFourierKernel K σ τ hστ ξ v).variation ≤
      P K hJ (scalarQuery σ τ hστ v.1
        (by simpa only [movingDomain_stationary] using v.2)) := by
  have h := intervalFourierKernel_variation_le K σ τ hστ ξ v
  rw [interval_firstMarginal_eq_parabolic hJ K B hp σ τ hστ v.1 0] at h
  exact h

/-- The ambient Fourier measure is supported on the actual interval. -/
theorem intervalFourierKernel_support {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1)) (hE : MeasurableSet E) :
    intervalFourierKernel K σ τ hστ ξ v E =
      intervalFourierKernel K σ τ hστ ξ v (E ∩ PDE.oneDimensionalAxisBox a c) := by
  simpa only [movingDomain_stationary] using
    fourierProjection_support hJ K _ ξ _ (intervalFourierKernel_spec K σ τ hστ ξ v) E hE

/-- The supported ambient measure has a unique lift to the actual terminal interval fiber. -/
theorem existsUnique_intervalFourierKernel_fiber {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) :
    ∃! μ : ComplexMeasure (EvolutionPosition (PDE.oneDimensionalAxisBox a c) stationary τ),
      μ.map Subtype.val = intervalFourierKernel K σ τ hστ ξ v :=
  existsUnique_fourierProjection_subtype hJ K _ ξ _
    (intervalFourierKernel_spec K σ τ hστ ξ v)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
