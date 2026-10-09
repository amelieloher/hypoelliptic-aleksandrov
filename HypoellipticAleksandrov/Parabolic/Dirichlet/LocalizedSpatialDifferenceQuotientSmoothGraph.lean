module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffGradientSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientWeakTest
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-!
# Localized quotient smooth graph compatibility

This module identifies each `L²` gradient coordinate of the localized spatial
difference quotient of a bundled smooth test with its two quotient-level
product-rule terms.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The smooth localized quotient has the expected coordinatewise `L²`
product-rule representative in the spatial Sobolev jet. -/
theorem localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ))) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) +
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) := by
  apply MeasureTheory.Lp.ext
  have hleftCoord := PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ)))
  have hleftJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ) j
  have hvalueJet := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hgradientCoord := PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))
  have hgradientJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j
  have hgradientRep : ⇑(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
      =ᵐ[PDE.volumeOn Ω] fun y => φ.partialDeriv j y := by
    exact hgradientCoord.trans hgradientJet
  have hfirst := cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η j k h
    (valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) φ hvalueJet hηshift
  have hsecond := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
    (fun y => φ.partialDeriv j y) hgradientRep hηshift
  have hadd := MeasureTheory.Lp.coeFn_add
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
    (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) )
  filter_upwards [hleftCoord, hleftJet, hfirst, hsecond, hadd] with y hleftCoord
      hleftJet hfirst hsecond hadd
  rw [hleftCoord, hleftJet,
    localizedSpatialDifferenceQuotientWeakTest_partialDeriv, hadd]
  simp only [Pi.add_apply]
  rw [hfirst, hsecond]
  rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
