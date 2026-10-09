module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry
public import HypoellipticAleksandrov.Parabolic.SpatialDirectionalDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.SpatialFDerivNorm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Uniform reverse-time raw-amplitude majorants

This module turns the literal pointwise spatial derivative majorants from the
Caccioppoli estimate into the signed raw coefficient bounds required by
the localized difference-quotient argument.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set
open scoped Matrix.Norms.Elementwise

/-- Literal spatial derivative and value majorants on the fixed coordinate
carrier give all signed raw reverse-time amplitudes used by the Caccioppoli
commutator. -/
theorem reverseTimeSpatialSignedRawAmplitude_bounds_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kχ : ℝ}
    (r₀ r₁ : ℝ) (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ)
    (δ M : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialMatrixFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
    (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
    (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialVectorFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
    (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
    (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
    (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M) :
    (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F z.1 z.2))
        (τ, y)| ≤ M) ∧
    (∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2))
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2))
        (τ, y)| ≤ M) := by
  classical
  let Q : Set (TimeVelocity d) := Set.Icc 0 (r₁ - r₀) ×ˢ
    spatialCoordinateShiftCarrier (tsupport χ.toFun) δ
  have hQreverse : reverseTimeMap r₁ '' Q ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro w ⟨z, hz, rfl⟩
    rw [mem_scalarParabolicClosedCylinder_iff]
    refine ⟨?_, ?_, subset_closure (hcarrier hz.2)⟩
    · simp only [reverseTimeMap_apply]
      linarith [hz.1.2]
    · simp only [reverseTimeMap_apply]
      linarith [hz.1.1]
  have hAderiv (i j : Fin d) : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) w := by
    intro w hw
    change DifferentiableAt ℝ
      (((fun z : TimeVelocity d => a z.1 z.2 i j) ∘ reverseTimeMap r₁)) w
    exact IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse
        (IsSmoothOnNeighborhood.coefficientEntry a ha i j)) hw
  have hBderiv (j : Fin d) : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) w := by
    intro w hw
    change DifferentiableAt ℝ
      (((fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j -
        b z.1 z.2 j) ∘ reverseTimeMap r₁)) w
    exact IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse
        (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)) hw
  have hqderiv : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2)) w := by
    intro w hw
    change DifferentiableAt ℝ (-((fun z : TimeVelocity d => c z.1 z.2) ∘ reverseTimeMap r₁)) w
    exact (IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse hc) hw).neg
  have hfderiv : ∀ w ∈ Q, DifferentiableAt ℝ
      (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F z.1 z.2)) w := by
    intro w hw
    change DifferentiableAt ℝ (-((fun z : TimeVelocity d => F z.1 z.2) ∘ reverseTimeMap r₁)) w
    exact (IsSmoothOnNeighborhood.differentiableAt
      (IsSmoothOnNeighborhood.reverseTime r₁ hQreverse hF) hw).neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h hh
    exact mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  · intro k h τ y hh hτ hy
    apply abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    · intro w hw
      exact hfderiv w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
        k (τ, y) hh ⟨hτ, hy⟩ hw)
    · intro w hw
      exact (abs_spatialScalarFDeriv_le _ w k).trans
        (hfD w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
          k (τ, y) hh ⟨hτ, hy⟩ hw))
  · intro i j k h τ y hh hτ hy
    apply abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    · intro w hw
      exact hAderiv i j w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
        k (τ, y) hh ⟨hτ, hy⟩ hw)
    · intro w hw
      exact (abs_spatialMatrixFDeriv_le _ w i j k).trans
        (hA w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
          k (τ, y) hh ⟨hτ, hy⟩ hw))
  · intro j k h τ y hh hτ hy
    have hshift : spatialShift k h (τ, y) ∈ Q := by
      refine ⟨?_, mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le hy hh⟩
      simpa only [spatialShift_apply] using hτ
    rw [spatialTranslate_apply]
    exact (PDE.abs_apply_le_vecEuclideanNorm
      (reverseTimeDivergenceDrift r₁ a b (spatialShift k h (τ, y)).1
        (spatialShift k h (τ, y)).2) j).trans (hB _ hshift)
  · intro j k h τ y hh hτ hy
    apply abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    · intro w hw
      exact hBderiv j w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
        k (τ, y) hh ⟨hτ, hy⟩ hw)
    · intro w hw
      exact (abs_spatialVectorFDeriv_le _ w j k).trans
        (hBD w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
          k (τ, y) hh ⟨hτ, hy⟩ hw))
  · intro k h τ y hh hτ hy
    have hshift : spatialShift k h (τ, y) ∈ Q := by
      refine ⟨?_, mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le hy hh⟩
      simpa only [spatialShift_apply] using hτ
    rw [spatialTranslate_apply]
    exact hq _ hshift
  · intro k h τ y hh hτ hy
    apply abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    · intro w hw
      exact hqderiv w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
        k (τ, y) hh ⟨hτ, hy⟩ hw)
    · intro w hw
      exact (abs_spatialScalarFDeriv_le _ w k).trans
        (hqD w (segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
          k (τ, y) hh ⟨hτ, hy⟩ hw))

/-- The raw-amplitude bounds in the sign convention consumed by the existing
nonprincipal remainder are the immediate sign corollary of the signed bridge. -/
theorem reverseTimeSpatialRawAmplitude_bounds_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kχ : ℝ}
    (r₀ r₁ : ℝ) (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ)
    (δ M : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialMatrixFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
    (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
    (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialVectorFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
    (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
    (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
    (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M) :
    (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => F (r₁ - z.1) z.2) (τ, y)| ≤ M) ∧
    (∀ (i j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (j k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
        (τ, y)| ≤ M) ∧
    (∀ (k : Fin d) (h τ : ℝ) (y : PDE.Vec d), |h| ≤ δ →
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
        (τ, y)| ≤ M) := by
  rcases reverseTimeSpatialSignedRawAmplitude_bounds_of_majorants r₀ r₁ χ δ M
    hcarrier a b c F ha hb hc hF hA hB hBD hq hqD hfD with
    ⟨hmap, hf, hA', hBT, hBD', hqT, hqD'⟩
  refine ⟨hmap, ?_, hA', hBT, hBD', ?_, ?_⟩
  · intro k h τ y hh hτ hy
    have hneg := hf k h τ y hh hτ hy
    have hsign : (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F z.1 z.2)) =
        -(fun z : TimeVelocity d => F (r₁ - z.1) z.2) := by
      funext z
      simp only [reverseTimeScalarCoefficient_apply, Pi.neg_apply]
    rw [hsign, spatialDifferenceQuotient_neg] at hneg
    simpa only [Pi.neg_apply, abs_neg] using hneg
  · intro k h τ y hh hτ hy
    have hneg := hqT k h τ y hh hτ hy
    have hsign : (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2)) =
        -(fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2) := by
      funext z
      simp only [Pi.neg_apply]
    rw [hsign, spatialTranslate_neg] at hneg
    simpa only [Pi.neg_apply, abs_neg] using hneg
  · intro k h τ y hh hτ hy
    have hneg := hqD' k h τ y hh hτ hy
    have hsign : (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2)) =
        -(fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2) := by
      funext z
      simp only [Pi.neg_apply]
    rw [hsign, spatialDifferenceQuotient_neg] at hneg
    simpa only [Pi.neg_apply, abs_neg] using hneg

end HypoellipticAleksandrov.Parabolic.Dirichlet
