module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.NestedCutoffLocality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialDifferenceQuotientBounds

/-!
# Definition of the nonprincipal localized commutator remainder

This leaf contains only the six-term scalar quantity used by the fixed-time
localized spatial-difference-quotient commutator.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The six nonprincipal terms in the fixed-time localized reverse-time
commutator, with the scalar time test deliberately factored out. -/
noncomputable def localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z =>
    reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.Vec d → ℝ := fun y =>
    η y * spatialDifferenceQuotient k h source (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y =>
    χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    χ y * spatialDifferenceQuotient k h γ (τ, y)
  (- (∫ y in Ω, sourceD y * (V y) ∂volume)) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      ((aD i j y * U j y) * (H i y)) ∂volume) -
    (∑ j : Fin d, ∫ y in Ω,
      ((driftT j y * E j y) * (V y)) ∂volume) -
    (∑ j : Fin d, ∫ y in Ω,
      ((driftD j y * U j y) * (V y)) ∂volume) +
    (∫ y in Ω, (γT y * V y) * (V y) ∂volume) +
    (∫ y in Ω, (γD y * U₀ y) * (V y) ∂volume)

end HypoellipticAleksandrov.Parabolic.Dirichlet
