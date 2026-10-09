module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionOccupation

/-! # Fourier decay on the zero-extension carrier

Interior Fourier measures are unchanged. Exterior ones vanish. Thus the proved
interval killing and frequency decay apply on the full ambient starting carrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped ENNReal

/-- Interior Fourier measures of the carrier adapter are exactly the interval Fourier measures. -/
theorem intervalExtension_fourier_inside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) :
    fourierKernel (intervalExtension hJ K) σ τ hστ ξ v.1 =
      intervalFourierKernel K σ τ hστ ξ v := by
  have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v.1 0) =
      K.master (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2)) := by
    change intervalExtensionMaster hJ K (intervalQueryInclusion
      (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2))) = _
    exact intervalExtensionMaster_inside hJ K _
  apply VectorMeasure.ext
  intro E hE
  rw [fourierKernel_spec _ _ _ _ _ _ E hE,
    intervalFourierKernel_spec _ _ _ _ _ _ E hE, he]
  rfl

/-- Exterior Fourier measures of the carrier adapter vanish. -/
theorem intervalExtension_fourier_outside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    fourierKernel (intervalExtension hJ K) σ τ hστ ξ v = 0 := by
  have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v 0) = 0 :=
    intervalExtensionMaster_outside hJ K _ hv
  apply VectorMeasure.ext
  intro E hE
  rw [fourierKernel_spec _ _ _ _ _ _ E hE, he]
  simp only [Measure.restrict_zero, integral_zero_measure, zero_apply]

/-- The uniform interval killing and frequency decay also hold for the carrier adapter. -/
theorem intervalExtension_fourier_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1),
    totalVariationNorm (fourierKernel (intervalExtension hJ K) σ τ hστ ξ v) ≤
      ENNReal.ofReal (C * Real.exp (-k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
  obtain ⟨C, k, hC, hk, hdec⟩ := interval_fourier_decay hH hLE lam Lam m Lb length
    hlam hlamLam hm hmLb hlength
  refine ⟨C, k, hC, hk, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ τ hστ ξ v
  by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
  · rw [intervalExtension_fourier_inside hJ K σ τ hστ ξ ⟨v, hv⟩]
    have h := hdec a c hac B b hs hJ S K hr hlen σ τ hστ v ξ
      (by simpa only [movingDomain_stationary] using hv) _
      (intervalFourierKernel_spec K σ τ hστ ξ ⟨v, hv⟩)
    rw [← ENNReal.ofReal_toReal
      (show totalVariationNorm (intervalFourierKernel K σ τ hστ ξ ⟨v, hv⟩) ≠ ⊤ from
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ ⟨v, hv⟩))]
    exact ENNReal.ofReal_le_ofReal h
  · rw [intervalExtension_fourier_outside hJ K σ τ hστ ξ v hv]
    simp only [totalVariationNorm, VectorMeasure.variation_zero, Measure.coe_zero, Pi.zero_apply,
      zero_le]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
