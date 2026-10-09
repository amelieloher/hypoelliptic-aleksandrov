module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.NestedCutoffLocality

/-!
# Plateau locality for localized spatial difference quotients

This module shows that a larger quantitative cutoff acts as the identity on
the value and gradient-coordinate restricted-`L²` classes of a localized
spatial difference quotient whose smaller cutoff is supported in its plateau.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A smooth cutoff is almost everywhere strongly measurable on restricted volume. -/
theorem cutoffL2Multiplier_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K) :
    AEStronglyMeasurable χ.toFun (PDE.volumeOn Ω) :=
  χ.smooth.continuous.aestronglyMeasurable

/-- A quantitative cutoff has norm at most one almost everywhere. -/
theorem cutoffL2Multiplier_norm_le_one
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖χ.toFun y‖ ≤ (1 : ℝ) :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg y)]
    exact χ.le_one y

private theorem cutoffGradient_eq_zero_of_not_mem_tsupport
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (i : Fin d)
    {y : PDE.Vec d} (hy : y ∉ tsupport η.toFun) :
    PDE.classicalGradient η.toFun y i = 0 := by
  rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
  exact ContinuousLinearMap.zero_apply _

/-- Multiplication by a quantitative spatial cutoff on restricted `L²`. -/
noncomputable def cutoffL2Multiplier
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  scalarL2Multiplier χ.toFun (cutoffL2Multiplier_aestronglyMeasurable χ) 1
    zero_le_one (cutoffL2Multiplier_norm_le_one χ)

/-- The cutoff multiplier is represented almost everywhere by pointwise
multiplication. -/
theorem cutoffL2Multiplier_apply_ae
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (χ : PDE.QuantitativeSmoothCutoff inner outer K)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(cutoffL2Multiplier (Ω := Ω) χ f) =ᵐ[PDE.volumeOn Ω]
      fun y => χ y * f y := by
  exact scalarL2Multiplier_apply_ae χ.toFun
    (cutoffL2Multiplier_aestronglyMeasurable χ) 1 zero_le_one
    (cutoffL2Multiplier_norm_le_one χ) f

private theorem cutoffL2Multiplier_apply_localizedSpatialDifferenceQuotientL2
    {d : ℕ}
    {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)}
    {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (hΩ : MeasurableSet Ω) (k : Fin d) (h : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    cutoffL2Multiplier (Ω := Ω) χ
        (localizedSpatialDifferenceQuotientL2 hΩ η k h f) =
      localizedSpatialDifferenceQuotientL2 hΩ η k h f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cutoffL2Multiplier_apply_ae χ
    (localizedSpatialDifferenceQuotientL2 hΩ η k h f),
    localizedSpatialDifferenceQuotientL2_apply_ae hΩ η k h f] with y hχ hη
  rw [hχ, hη, localizedSpatialDifferenceQuotient_apply]
  by_cases hy : η y = 0
  · simp [hy]
  · rw [χ.eq_one_on_inner y (hηχ (subset_tsupport η.toFun hy)), one_mul]

private theorem
    cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    {d : ℕ}
    {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)}
    {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (hΩ : MeasurableSet Ω) (i k : Fin d) (h : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    cutoffL2Multiplier (Ω := Ω) χ
        (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f) =
      cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cutoffL2Multiplier_apply_ae χ
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ η i k h f),
    cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η i k h f] with y hχ hη
  rw [hχ, hη]
  by_cases hy : y ∈ tsupport η.toFun
  · rw [χ.eq_one_on_inner y (hηχ hy), one_mul]
  · rw [cutoffGradient_eq_zero_of_not_mem_tsupport η i hy]
    ring

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
  have hgradient := congrArg (fun T : H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (T u))
    (gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM
      hΩ η k h hηΩ hηshift)
  simpa only [ContinuousLinearMap.comp_apply,
    localizedSpatialDifferenceQuotientSmoothGradientCLM,
    ContinuousLinearMap.add_apply,
    PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble] using hgradient

/-- A larger plateau cutoff fixes the value of the localized spatial
difference quotient in restricted `L²`. -/
theorem
    cutoffL2Multiplier_apply_valueCLM_localizedSpatialDifferenceQuotientH10CLM
    {d : ℕ}
    {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)}
    {Kη Kχ : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffL2Multiplier (Ω := Ω) χ
        (valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h hηΩ hηshift u)) =
      valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift u) := by
  have hvalue := congrArg (fun T : H10HilbertGraph hΩ →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) => T u)
    (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM
      hΩ η k h hηΩ hηshift)
  have hvalue' :
      valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u) =
        localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ u) := by
    simpa only [ContinuousLinearMap.comp_apply] using hvalue
  change cutoffL2Multiplier (Ω := Ω) χ
      (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) = _
  rw [hvalue']
  exact cutoffL2Multiplier_apply_localizedSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet k h (valueCLM hΩ u)

/-- A larger plateau cutoff fixes every weak-gradient coordinate of the
localized spatial difference quotient in restricted `L²`. -/
theorem
    cutoffL2Multiplier_apply_gradientCoordCLM_localizedSpatialDifferenceQuotientH10CLM
    {d : ℕ}
    {Ω innerη outerη innerχ outerχ : Set (PDE.Vec d)}
    {Kη Kχ : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff innerη outerη Kη)
    (χ : PDE.QuantitativeSmoothCutoff innerχ outerχ Kχ)
    (hηχ : tsupport η.toFun ⊆ innerχ)
    (i k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    cutoffL2Multiplier (Ω := Ω) χ
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h hηΩ hηshift u))) =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h hηΩ hηshift u)) := by
  rw [gradientCoord_localizedSpatialDifferenceQuotientH10CLM_eq
    hΩ η k h hηΩ hηshift i u]
  rw [map_add]
  rw [cutoffL2Multiplier_apply_cutoffGradientSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet i k h (valueCLM hΩ u)]
  rw [cutoffL2Multiplier_apply_localizedSpatialDifferenceQuotientL2
    η χ hηχ hΩ.measurableSet k h
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u))]

end HypoellipticAleksandrov.Parabolic.Dirichlet
