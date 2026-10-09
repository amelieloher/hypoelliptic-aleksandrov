module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-!
# Smooth localized energy-test representations

This module expands the reverse-time spatial form and source functional on a
smooth localized energy test into their literal spatial integral formulas.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time spatial form on a smooth input and its localized energy
test is the literal principal, divergence-drift, and scalar integral sum. -/
theorem reverseTimeSpatialForm_apply_smooth_localizedSpatialDifferenceQuotientEnergyTest_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    reverseTimeSpatialForm hΩ r₁ τ a b c
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j * φ.partialDeriv j y *
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift).partialDeriv i y ∂volume) +
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j * φ.partialDeriv j y *
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift) y ∂volume) -
      ∫ y in Ω,
        reverseTimeScalarCoefficient r₁ c τ y * φ y *
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift) y ∂volume := by
  have hinput :
      smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
        smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  rw [localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth
      hΩ η k h φ hηΩ hηshift,
    reverseTimeSpatialForm_apply, hinput]
  have hprincipal (i j : Fin d) :
      (∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ
              (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) y *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ
              (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
                (localizedSpatialDifferenceQuotientEnergyWeakTest
                  η k h φ φ.contDiff hηΩ hηshift)))) y) =
        ∫ y in Ω,
          a (r₁ - τ) y i j * φ.partialDeriv j y *
            (localizedSpatialDifferenceQuotientEnergyWeakTest
              η k h φ φ.contDiff hηΩ hηshift).partialDeriv i y := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)),
        ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j,
        PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
              (localizedSpatialDifferenceQuotientEnergyWeakTest
                η k h φ φ.contDiff hηΩ hηshift))),
        ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift) i] with y hφj hφ hψi hψ
    rw [hφj, hφ, hψi, hψ]
  have hdrift (j : Fin d) :
      (∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ
              (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
              (localizedSpatialDifferenceQuotientEnergyWeakTest
                η k h φ φ.contDiff hηΩ hηshift))) y) =
        ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j * φ.partialDeriv j y *
            (localizedSpatialDifferenceQuotientEnergyWeakTest
              η k h φ φ.contDiff hηΩ hηshift) y := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)),
        ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j,
        ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift)] with y hφj hφ hψ
    rw [hφj, hφ, hψ]
  have hscalar :
      (∫ y in Ω,
        reverseTimeScalarCoefficient r₁ c τ y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
              (localizedSpatialDifferenceQuotientEnergyWeakTest
                η k h φ φ.contDiff hηΩ hηshift))) y) =
        ∫ y in Ω,
          reverseTimeScalarCoefficient r₁ c τ y * φ y *
            (localizedSpatialDifferenceQuotientEnergyWeakTest
              η k h φ φ.contDiff hηΩ hηshift) y := by
    apply integral_congr_ae
    filter_upwards
      [ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ,
        ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientEnergyWeakTest
            η k h φ φ.contDiff hηΩ hηshift)] with y hφ hψ
    rw [hφ, hψ]
  simp_rw [hprincipal, hdrift, hscalar]

/-- The reverse-time source functional on a smooth localized energy test is
the literal negative source integral. -/
theorem reverseTimeSourceFunctional_apply_smooth_localizedSpatialDifferenceQuotientEnergyTest_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : MeasureTheory.MemLp
      (fun y : PDE.Vec d => F (r₁ - τ) y)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω))
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    reverseTimeSourceFunctional hΩ
        (reverseTimeSourceSlice r₁ τ F hF)
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) =
      -∫ y in Ω, F (r₁ - τ) y *
        (localizedSpatialDifferenceQuotientEnergyWeakTest
          η k h φ φ.contDiff hηΩ hηshift) y ∂volume := by
  rw [reverseTimeSourceFunctional_apply,
    localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth
      hΩ η k h φ hηΩ hηshift,
    L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards
    [coeFn_reverseTimeSourceSlice r₁ τ F hF,
      ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest
          η k h φ φ.contDiff hηΩ hηshift)] with y hF hψ
  rw [hψ, hF]
  simp only [RCLike.inner_apply, conj_trivial]

end HypoellipticAleksandrov.Parabolic.Dirichlet
