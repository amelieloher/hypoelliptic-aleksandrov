module

public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise

/-!
# Localized spatial difference quotients on restricted `L²`

This module constructs the representative-independent cutoff-weighted forward
spatial difference quotient using ambient zero extension, translation,
restriction, and multiplication on quotient `L²` spaces.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A smooth cutoff is almost everywhere strongly measurable on restricted volume. -/
theorem cutoff_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
  η.smooth.continuous.aestronglyMeasurable

/-- A quantitative smooth cutoff has norm at most one almost everywhere. -/
theorem cutoff_norm_le_one
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖η.toFun y‖ ≤ (1 : ℝ) :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
    exact η.le_one y

/-- The representative-independent cutoff-weighted forward spatial difference
quotient on restricted-volume scalar `L²`. -/
noncomputable def localizedSpatialDifferenceQuotientL2
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  let μ : Measure (PDE.Vec d) := volume
  let z : PDE.Vec d := h • PDE.basisVec k
  let T : PDE.Vec d → PDE.Vec d := fun y => y + z
  let hT : MeasurePreserving T μ μ :=
    measurePreserving_add_right μ z
  let E : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.zeroExtendLinearIsometry (μ := μ) hΩ).toContinuousLinearMap
  let P : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ]
      Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  let R : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ μ (2 : ℝ≥0∞) Ω
  let M : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    scalarL2Multiplier η.toFun (cutoff_aestronglyMeasurable η) 1 zero_le_one
      (cutoff_norm_le_one η)
  h⁻¹ • M.comp (R.comp (P.comp E - E))

/-- The restricted-space quotient agrees almost everywhere with the canonical
zero-extension representative formula. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      fun y => localizedSpatialDifferenceQuotient η k h
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)) y := by
  unfold localizedSpatialDifferenceQuotientL2
  dsimp
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k)))
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          fun y : PDE.Vec d => y + h • PDE.basisVec k) := by
    change MeasureTheory.Lp.compMeasurePreserving
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (h • PDE.basisVec k)) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          fun y : PDE.Vec d => y + h • PDE.basisVec k)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving
      ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (h • PDE.basisVec k))
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hM := scalarL2Multiplier_apply_ae η.toFun
    (cutoff_aestronglyMeasurable η) 1 zero_le_one
    (cutoff_norm_le_one η)
    ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul h⁻¹
    ((scalarL2Multiplier η.toFun (cutoff_aestronglyMeasurable η) 1 zero_le_one
      (cutoff_norm_le_one η)
      ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))))
  filter_upwards [hsmul, hM, hR, hsub.restrict, hP.restrict] with y hsmul hM hR hsub hP
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hM, hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- A supplied restricted-space representative may replace the canonical zero
extension on the cutoff's forward active collar. -/
theorem localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ η k h f) =ᵐ[PDE.volumeOn Ω]
      localizedSpatialDifferenceQuotient η k h g := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f
  have hfg' := ae_imp_of_ae_restrict hfg
  have hambient : ∀ᵐ y : PDE.Vec d ∂volume,
      y ∈ Ω → ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y := by
    filter_upwards [hzero, hfg'] with y hzero hfg hy
    rw [hzero, Set.indicator_of_mem hy]
    exact hfg hy
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (h • PDE.basisVec k)).quasiMeasurePreserving.ae hambient
  have hambientOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      y ∈ Ω → ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y :=
    (ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)
  have hshiftedOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      y + h • PDE.basisVec k ∈ Ω →
        ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
          (y + h • PDE.basisVec k) = g (y + h • PDE.basisVec k) :=
    (ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy)
  have hmem : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, y ∈ Ω :=
    (ae_restrict_iff' hΩ).mpr (ae_of_all _ fun y hy => hy)
  filter_upwards [localizedSpatialDifferenceQuotientL2_apply_ae hΩ η k h f,
    hambientOn, hshiftedOn, hmem] with y hq hy hyshift hymem
  rw [hq, localizedSpatialDifferenceQuotient_apply]
  by_cases hη : η.toFun y = 0
  · simp [hη]
  have hysupport : y ∈ tsupport η.toFun :=
    subset_tsupport η.toFun hη
  have hyshiftmem : y + h • PDE.basisVec k ∈ Ω := hηshift hysupport
  rw [hy hymem, hyshift hyshiftmem]
  rfl

/-- The localized quotient has the sharp totalized `L²` application bound. -/
theorem norm_localizedSpatialDifferenceQuotientL2_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖localizedSpatialDifferenceQuotientL2 hΩ η k h f‖ ≤
      (2 / |h|) * ‖f‖ := by
  by_cases hh : h = 0
  · subst h
    simp [localizedSpatialDifferenceQuotientL2]
  unfold localizedSpatialDifferenceQuotientL2
  dsimp
  have hM := norm_scalarL2Multiplier_apply_le η.toFun
    (cutoff_aestronglyMeasurable η) 1 zero_le_one (cutoff_norm_le_one η)
    ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  have hR : ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤
      ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := by
    exact norm_Lp_toLp_restrict_le Ω _
  have hD : ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ ≤ 2 * ‖f‖ := by
    calc
      _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ +
          ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by
        rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
        ring
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  have hM' : ‖(scalarL2Multiplier η.toFun (cutoff_aestronglyMeasurable η)
      1 zero_le_one (cutoff_norm_le_one η)
      ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) )‖ ≤
      ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ := by
    simpa using hM
  have hR' := hR.trans hD
  calc
    _ ≤ |h|⁻¹ * ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ :=
      mul_le_mul_of_nonneg_left hM' (inv_nonneg.mpr (abs_nonneg h))
    _ ≤ |h|⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left hR' (inv_nonneg.mpr (abs_nonneg h))
    _ = (2 / |h|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

/-- The localized quotient operator norm is bounded by its totalized sharp
`L²` constant. -/
theorem norm_localizedSpatialDifferenceQuotientL2_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    ‖localizedSpatialDifferenceQuotientL2 hΩ η k h‖ ≤ 2 / |h| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact norm_localizedSpatialDifferenceQuotientL2_apply_le hΩ η k h f

end HypoellipticAleksandrov.Parabolic.Dirichlet
