module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCommutator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient

/-!
# Smooth core for the arbitrary-`H¹₀` commutator

This module records the literal fixed-step commutator expression and proves it
on the dense compactly supported smooth core.  The arbitrary-`H¹₀` lifting
and its localized-field infrastructure remain in the canonical commutator
module.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (i : Fin d) (u : H10HilbertGraph hΩ) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) +
        localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u)) := by
  have hgrad := congrArg (fun T : H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (T u))
    (gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM
      hΩ η k h hηΩ hηshift)
  simpa only [ContinuousLinearMap.comp_apply,
    localizedSpatialDifferenceQuotientSmoothGradientCLM,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,
    PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble] using hgrad

private theorem outerCutoff_mul_innerCutoff_eq
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (y : PDE.Vec d) :
    χ y * η y = η y := by
  by_cases hy : η y = 0
  · simp [hy]
  · have hysupport : y ∈ tsupport η.toFun := subset_tsupport η.toFun hy
    rw [χ.eq_one_on_inner y hysupport, one_mul]

private theorem outerCutoff_mul_innerCutoffGradient_eq
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (i : Fin d) (y : PDE.Vec d) :
    χ y * PDE.classicalGradient η.toFun y i =
      PDE.classicalGradient η.toFun y i := by
  by_cases hy : y ∈ tsupport η.toFun
  · rw [χ.eq_one_on_inner y hy, one_mul]
  · rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
    simp

private def h10CommutatorLhs
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))

private def h10CommutatorRawLeaf
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (sourceD V : PDE.Vec d → ℝ)
    (aT aD : Fin d → Fin d → PDE.Vec d → ℝ)
    (E H U : Fin d → PDE.Vec d → ℝ)
    (driftT driftD : Fin d → PDE.Vec d → ℝ)
    (γT γD U₀ : PDE.Vec d → ℝ) : ℝ :=
  -(∫ y in Ω, sourceD y * V y ∂volume) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (aT i j y * E j y + aD i j y * U j y) * H i y ∂volume) -
    (∑ j : Fin d, ∫ y in Ω,
      (driftT j y * E j y + driftD j y * U j y) * V y ∂volume) +
    ∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y ∂volume

private theorem fintype_sum_const_mul
    {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (∑ i, a * f i) = a * ∑ i, f i := by
  rw [Finset.mul_sum]

private theorem fintype_sum_sum_const_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ) (f : ι → κ → ℝ) :
    (∑ i, ∑ j, a * f i j) = a * ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ i, a * ∑ j, f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact fintype_sum_const_mul a (f i)
    _ = _ := fintype_sum_const_mul a (fun i => ∑ j, f i j)

private def h10CommutatorRawRhs
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y => η y *
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.Vec d → ℝ := fun y => ζ τ * η y *
    spatialDifferenceQuotient k h source (τ, y)
  let aT : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    ζ τ * χ y * spatialDifferenceQuotient k h γ (τ, y)
  h10CommutatorRawLeaf (Ω := Ω) sourceD V aT aD E H U driftT driftD γT γD U₀

private theorem h10CommutatorRawRhs_eq_leaf
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u =
      h10CommutatorRawLeaf (Ω := Ω)
        (fun y => ζ τ * η y * spatialDifferenceQuotient k h
          (fun z => F (r₁ - z.1) z.2) (τ, y))
        (fun y => valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u) y)
        (fun i j y => ζ τ * χ y * spatialTranslate k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y))
        (fun i j y => ζ τ * χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y))
        (fun i y =>
          PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)) y -
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
              (valueCLM hΩ u) y)
        (fun i y =>
          PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)) y +
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
              (valueCLM hΩ u) y)
        (fun j y => η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ u) y)
        (fun j y => ζ τ * χ y * spatialTranslate k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y))
        (fun j y => ζ τ * χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y))
        (fun y => ζ τ * χ y * spatialTranslate k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y))
        (fun y => ζ τ * χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y))
        (fun y => η y * valueCLM hΩ u y) := rfl

/-- The literal fixed-step H¹₀ commutator identity. -/
def h10CommutatorFixedStepOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : Prop :=
        let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let V : PDE.Vec d → ℝ :=
          fun y => valueCLM hΩ (A u) y
        let G : Fin d → PDE.Vec d → ℝ :=
          fun i y =>
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
              (gradientCLM hΩ (A u)) y
        let W : Fin d → PDE.Vec d → ℝ :=
          fun i y =>
            cutoffGradientSpatialDifferenceQuotientL2
              hΩ.measurableSet η i k h (valueCLM hΩ u) y
        let E : Fin d → PDE.Vec d → ℝ :=
          fun i y => G i y - W i y
        let H : Fin d → PDE.Vec d → ℝ :=
          fun i y => G i y + W i y
        let U : Fin d → PDE.Vec d → ℝ :=
          fun j y =>
            η y *
              PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                (gradientCLM hΩ u) y
        let U₀ : PDE.Vec d → ℝ :=
          fun y => η y * valueCLM hΩ u y
        let source : TimeVelocity d → ℝ :=
          fun z => F (r₁ - z.1) z.2
        let α : Fin d → Fin d → TimeVelocity d → ℝ :=
          fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
        let drift : Fin d → TimeVelocity d → ℝ :=
          fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
        let γ : TimeVelocity d → ℝ :=
          fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
        let sourceD : PDE.Vec d → ℝ :=
          fun y =>
            ζ τ * η y *
              spatialDifferenceQuotient k h source (τ, y)
        let aT : Fin d → Fin d → PDE.Vec d → ℝ :=
          fun i j y =>
            ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
        let aD : Fin d → Fin d → PDE.Vec d → ℝ :=
          fun i j y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h (α i j) (τ, y)
        let driftT : Fin d → PDE.Vec d → ℝ :=
          fun j y =>
            ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
        let driftD : Fin d → PDE.Vec d → ℝ :=
          fun j y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h (drift j) (τ, y)
        let γT : PDE.Vec d → ℝ :=
          fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
        let γD : PDE.Vec d → ℝ :=
          fun y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h γ (τ, y)
        ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) =
          -(∫ y in Ω, sourceD y * V y ∂volume) -
            (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
              (aT i j y * E j y + aD i j y * U j y) *
                H i y ∂volume) -
            (∑ j : Fin d, ∫ y in Ω,
              (driftT j y * E j y + driftD j y * U j y) *
                V y ∂volume) +
            ∫ y in Ω,
              (γT y * V y + γD y * U₀ y) * V y ∂volume

private def smoothCoreFactoredExpression
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ}
    (r₀ r₁ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ) (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ) (φ : PDE.WeakTestFunction Ω) : ℝ :=
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let D : PDE.Vec d → ℝ := fun y =>
    (φ (y + h • PDE.basisVec k) - φ y) / h
  let Dg : Fin d → PDE.Vec d → ℝ := fun i y =>
    (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h
  let sourceSmooth : ℝ := ∫ y in Ω,
    spatialDifferenceQuotient k h source (τ, y) * η y ^ 2 * D y ∂volume
  let principalSmooth : Fin d → Fin d → ℝ := fun i j => ∫ y in Ω,
    (spatialTranslate k h (α i j) (τ, y) * Dg j y +
      spatialDifferenceQuotient k h (α i j) (τ, y) * φ.partialDeriv j y) *
      (2 * η y * PDE.classicalGradient η.toFun y i * D y + η y ^ 2 * Dg i y) ∂volume
  let driftSmooth : Fin d → ℝ := fun j => ∫ y in Ω,
    (spatialTranslate k h (drift j) (τ, y) * Dg j y +
      spatialDifferenceQuotient k h (drift j) (τ, y) * φ.partialDeriv j y) *
      (η y ^ 2 * D y) ∂volume
  let scalarSmooth : ℝ := ∫ y in Ω,
    (spatialTranslate k h γ (τ, y) * D y +
      spatialDifferenceQuotient k h γ (τ, y) * φ y) * (η y ^ 2 * D y) ∂volume
  ζ τ * (-sourceSmooth - (∑ i : Fin d, ∑ j : Fin d, principalSmooth i j) -
    (∑ j : Fin d, driftSmooth j) + scalarSmooth)

private theorem smoothCore_rawRhs_eq_factoredExpression
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCoreFactoredExpression r₀ r₁ a b c F ζ η k h τ φ := by
  rw [h10CommutatorRawRhs_eq_leaf]
  dsimp only [h10CommutatorRawLeaf, smoothCoreFactoredExpression]
  let u : H10HilbertGraph hΩ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let gc : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    fun i => (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i).comp (gradientCLM hΩ)
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y-W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y+W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y => η y*gc j u y
  let U₀ : PDE.Vec d → ℝ := fun y => η y*valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁-z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD := fun y => ζ τ*η y*spatialDifferenceQuotient k h source (τ,y)
  let aT := fun i j y => ζ τ*χ y*spatialTranslate k h (α i j) (τ,y)
  let aD := fun i j y => ζ τ*χ y*spatialDifferenceQuotient k h (α i j) (τ,y)
  let driftT := fun j y => ζ τ*χ y*spatialTranslate k h (drift j) (τ,y)
  let driftD := fun j y => ζ τ*χ y*spatialDifferenceQuotient k h (drift j) (τ,y)
  let γT := fun y => ζ τ*χ y*spatialTranslate k h γ (τ,y)
  let γD := fun y => ζ τ*χ y*spatialDifferenceQuotient k h γ (τ,y)
  let D := fun y => (φ (y+h•PDE.basisVec k)-φ y)/h
  let Dg := fun i y => (φ.partialDeriv i (y+h•PDE.basisVec k)-φ.partialDeriv i y)/h
  change
    -(∫ y in Ω, sourceD y * V y ∂volume) -
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (aT i j y * E j y + aD i j y * U j y) * H i y ∂volume) -
      (∑ j : Fin d, ∫ y in Ω,
        (driftT j y * E j y + driftD j y * U j y) * V y ∂volume) +
      ∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y ∂volume =
    ζ τ *
      (-(∫ y in Ω, spatialDifferenceQuotient k h source (τ, y) * η y ^ 2 * D y ∂volume) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          (spatialTranslate k h (α i j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (α i j) (τ, y) * φ.partialDeriv j y) *
            (2 * η y * PDE.classicalGradient η.toFun y i * D y +
              η y ^ 2 * Dg i y) ∂volume) -
        (∑ j : Fin d, ∫ y in Ω,
          (spatialTranslate k h (drift j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (drift j) (τ, y) * φ.partialDeriv j y) *
            (η y ^ 2 * D y) ∂volume) +
        ∫ y in Ω,
          (spatialTranslate k h γ (τ, y) * D y +
            spatialDifferenceQuotient k h γ (τ, y) * φ y) * (η y ^ 2 * D y) ∂volume)
  have hu : u = smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hv : ⇑(valueCLM hΩ u) =ᵐ[PDE.volumeOn Ω] φ := by
    rw [hu]
    exact ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hg i : ⇑(gc i u)=ᵐ[PDE.volumeOn Ω] fun y=>φ.partialDeriv i y := by
    dsimp only [gc,ContinuousLinearMap.comp_apply]; rw [hu]
    exact (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))).trans
        (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ i)
  have hV : V=ᵐ[PDE.volumeOn Ω] fun y=>η y*D y := by
    have q := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
      hΩ.measurableSet η k h (valueCLM hΩ u) φ hv hηshift
    have e : valueCLM hΩ (A u) =
        localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ u) := by
      change ((valueCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift)) u = _
      rw [valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM]
      rfl
    dsimp only [V]
    rw [e]
    filter_upwards [q] with y hy
    simpa only [localizedSpatialDifferenceQuotient_apply, D] using hy
  have hW i : W i=ᵐ[PDE.volumeOn Ω] fun y=>PDE.classicalGradient η.toFun y i*D y := by
    dsimp only [W]
    simpa only [D] using
      cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
        hΩ.measurableSet η i k h (valueCLM hΩ u) φ hv hηshift
  have hDg i :
      ⇑(localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (gc i u)) =ᵐ[PDE.volumeOn Ω]
        fun y => η y * Dg i y := by
    filter_upwards [localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
      hΩ.measurableSet η k h (gc i u) (fun y => φ.partialDeriv i y) (hg i) hηshift]
      with y hy
    simpa only [localizedSpatialDifferenceQuotient_apply, Dg] using hy
  have hG i : G i=ᵐ[PDE.volumeOn Ω] fun y=>PDE.classicalGradient η.toFun y i*D y+η y*Dg i y := by
    dsimp only [G]
    have hGClass : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ (A u)) =
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) +
          localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (gc i u) := by
      dsimp only [A, gc, ContinuousLinearMap.comp_apply]
      exact gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
        hΩ η k h η.tsupport_subset hηshift i u
    rw [hGClass]
    filter_upwards [MeasureTheory.Lp.coeFn_add
      (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u))
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (gc i u)),
      (show cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) =ᵐ[PDE.volumeOn Ω]
          fun y => PDE.classicalGradient η.toFun y i * D y by
        simpa only [W] using hW i), hDg i] with y ha hb hc
    rw [ha]
    simp only [Pi.add_apply]
    rw [hb, hc]
  have hE i : E i =ᵐ[PDE.volumeOn Ω] fun y => η y * Dg i y := by
    filter_upwards [hG i, hW i] with y hG' hW'
    dsimp only [E]
    rw [hG', hW']
    ring
  have hH i : H i =ᵐ[PDE.volumeOn Ω] fun y =>
      2 * PDE.classicalGradient η.toFun y i * D y + η y * Dg i y := by
    filter_upwards [hG i, hW i] with y hG' hW'
    dsimp only [H]
    rw [hG', hW']
    ring
  have hU i : U i =ᵐ[PDE.volumeOn Ω] fun y => η y * φ.partialDeriv i y := by
    filter_upwards [hg i] with y hgrad
    dsimp only [U, gc]
    rw [hgrad]
  have hU₀ : U₀ =ᵐ[PDE.volumeOn Ω] fun y => η y * φ y := by
    filter_upwards [hv] with y hvalue
    dsimp only [U₀]
    rw [hvalue]
  have hsourceFactor :
      (∫ y in Ω, sourceD y * V y ∂volume) =
        ζ τ * ∫ y in Ω,
          spatialDifferenceQuotient k h source (τ, y) * η y ^ 2 * D y ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hV] with y hV'
    rw [hV']
    dsimp only [sourceD]
    ring
  have hprincipalFactor (i j : Fin d) :
      (∫ y in Ω, (aT i j y * E j y + aD i j y * U j y) * H i y ∂volume) =
        ζ τ * ∫ y in Ω,
          (spatialTranslate k h (α i j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (α i j) (τ, y) * φ.partialDeriv j y) *
            (2 * η y * PDE.classicalGradient η.toFun y i * D y +
              η y ^ 2 * Dg i y) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hE j, hU j, hH i] with y hE' hU' hH'
    rw [hE', hU', hH']
    dsimp only [aT, aD]
    calc
      _ = ζ τ * (χ y * η y) *
          ((spatialTranslate k h (α i j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (α i j) (τ, y) * φ.partialDeriv j y) *
            (2 * PDE.classicalGradient η.toFun y i * D y + η y * Dg i y)) := by ring
      _ = _ := by rw [outerCutoff_mul_innerCutoff_eq η χ y]; ring
  have hdriftFactor (j : Fin d) :
      (∫ y in Ω, (driftT j y * E j y + driftD j y * U j y) * V y ∂volume) =
        ζ τ * ∫ y in Ω,
          (spatialTranslate k h (drift j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (drift j) (τ, y) * φ.partialDeriv j y) *
            (η y ^ 2 * D y) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hE j, hU j, hV] with y hE' hU' hV'
    rw [hE', hU', hV']
    dsimp only [driftT, driftD]
    calc
      _ = ζ τ * (χ y * η y) *
          ((spatialTranslate k h (drift j) (τ, y) * Dg j y +
            spatialDifferenceQuotient k h (drift j) (τ, y) * φ.partialDeriv j y) *
            (η y * D y)) := by ring
      _ = _ := by rw [outerCutoff_mul_innerCutoff_eq η χ y]; ring
  have hscalarFactor :
      (∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y ∂volume) =
        ζ τ * ∫ y in Ω,
          (spatialTranslate k h γ (τ, y) * D y +
            spatialDifferenceQuotient k h γ (τ, y) * φ y) *
            (η y ^ 2 * D y) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hV, hU₀] with y hV' hU₀'
    rw [hV', hU₀']
    dsimp only [γT, γD]
    calc
      _ = ζ τ * (χ y * η y) *
          ((spatialTranslate k h γ (τ, y) * D y +
            spatialDifferenceQuotient k h γ (τ, y) * φ y) * (η y * D y)) := by ring
      _ = _ := by rw [outerCutoff_mul_innerCutoff_eq η χ y]; ring
  rw [hsourceFactor, hscalarFactor]
  simp_rw [hprincipalFactor, hdriftFactor]
  rw [fintype_sum_sum_const_mul, fintype_sum_const_mul]
  ring

private theorem smoothCore_lhs_eq_factoredExpression
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCoreFactoredExpression r₀ r₁ a b c F ζ η k h τ φ := by
  dsimp only [h10CommutatorLhs, smoothCoreFactoredExpression]
  let u : H10HilbertGraph hΩ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let D : PDE.Vec d → ℝ := fun y =>
    (φ (y + h • PDE.basisVec k) - φ y) / h
  let Dg : Fin d → PDE.Vec d → ℝ := fun i y =>
    (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h
  have hsmooth := reverseTimeSource_sub_reverseTimeSpatialForm_smooth_energyTest_eq_commutator
    r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth τ hτ
      η k h φ η.tsupport_subset hηshift
  rw [reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτ]
  have hmul := congrArg (fun x : ℝ => ζ τ * x) hsmooth
  simpa only [B, u, source, α, drift, γ, D, Dg, spatialDifferenceQuotient_apply,
    spatialTranslate_apply, spatialShift_apply, reverseTimeCoefficient_apply,
    reverseTimeDivergenceDrift, reverseTimeScalarCoefficient_apply, mul_assoc] using hmul

/-- The literal fixed-step commutator identity on the dense smooth H¹₀ core. -/
theorem smoothCore_fixedStep_reverseTimeSource_sub_reverseTimeSpatialForm_eq_commutator
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorFixedStepOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
      hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  change h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
    h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  exact (smoothCore_lhs_eq_factoredExpression r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ η k h τ hηshift hτ φ).trans
    (smoothCore_rawRhs_eq_factoredExpression r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift φ).symm

end HypoellipticAleksandrov.Parabolic.Dirichlet
