module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import PDEFoundation.Measure.AffineVolume

/-!
# Cutoff-gradient spatial difference quotients on restricted `L²`

This module constructs the representative-independent scalar restricted-`L²`
operator `(D_j η) Δ_{k,h}` using ambient zero extension, global translation,
restriction, and the bounded scalar multiplier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A cutoff gradient coordinate is measurable for restricted volume. -/
theorem cutoffGradient_aestronglyMeasurable
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d) :
    AEStronglyMeasurable (fun y => PDE.classicalGradient η.toFun y j)
      (PDE.volumeOn Ω) := by
  have hcontinuous : Continuous (fun y => PDE.classicalGradient η.toFun y j) := by
    simpa only [PDE.classicalGradient_apply] using
      (η.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcontinuous.aestronglyMeasurable

/-- A cutoff gradient coordinate obeys the cutoff bound almost everywhere. -/
theorem cutoffGradient_norm_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d) :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖PDE.classicalGradient η.toFun y j‖ ≤ K :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]
    exact η.abs_classicalGradient_apply_le y j

private theorem cutoffGradient_eq_zero_of_not_mem_tsupport
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d)
    {y : PDE.Vec d} (hy : y ∉ tsupport η.toFun) :
    PDE.classicalGradient η.toFun y j = 0 := by
  rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
  exact ContinuousLinearMap.zero_apply _

/-- The cutoff-coordinate-gradient times forward spatial difference quotient
on restricted-volume scalar `L²`, totalized at zero increment. -/
noncomputable def cutoffGradientSpatialDifferenceQuotientL2
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) :
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
    scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y j)
      (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η j)
  h⁻¹ • M.comp (R.comp (P.comp E - E))

/-- The cutoff-gradient quotient uses the canonical global zero extension. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
              (y + h • PDE.basisVec k) -
            ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / h) := by
  unfold cutoffGradientSpatialDifferenceQuotientL2
  dsimp only
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, LinearIsometry.coe_toContinuousLinearMap]
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
  have hM := scalarL2Multiplier_apply_ae
    (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η j)
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
    ((scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y j)
      (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η j)
      ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))))
  filter_upwards [hsmul, hM, hR, hsub.restrict, hP.restrict] with y hsmul hM hR hsub hP
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hM, hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- A supplied representative gives the literal cutoff-gradient quotient
under the forward active-support collar. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((g (y + h • PDE.basisVec k) - g y) / h) := by
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
  filter_upwards [cutoffGradientSpatialDifferenceQuotientL2_apply_ae hΩ η j k h f,
    hambientOn, hshiftedOn, hmem] with y hq hy hyshift hymem
  rw [hq]
  by_cases hgradient : PDE.classicalGradient η.toFun y j = 0
  · have hgradient' : (fderiv ℝ η.toFun y) (PDE.basisVec j) = 0 := by
      simpa only [PDE.classicalGradient_apply] using hgradient
    simp [hgradient']
  have hysupport : y ∈ tsupport η.toFun := by
    by_contra hytsupport
    exact hgradient (cutoffGradient_eq_zero_of_not_mem_tsupport η j hytsupport)
  have hyshiftmem : y + h • PDE.basisVec k ∈ Ω := hηshift hysupport
  rw [hy hymem, hyshift hyshiftmem]

/-- The cutoff-gradient quotient has the totalized `L²` application bound. -/
theorem norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f‖ ≤
      (2 * K / |h|) * ‖f‖ := by
  by_cases hh : h = 0
  · subst h
    simp [cutoffGradientSpatialDifferenceQuotientL2]
  unfold cutoffGradientSpatialDifferenceQuotientL2
  dsimp only
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hM := norm_scalarL2Multiplier_apply_le
    (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
    (cutoffGradient_norm_le η j)
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
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  have hM' : ‖(scalarL2Multiplier (fun y => PDE.classicalGradient η.toFun y j)
      (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg
      (cutoffGradient_norm_le η j)
      ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) )‖ ≤
      K * ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ := by
    simpa using hM
  have hR' := hR.trans hD
  have hKR : K * ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤ K * (2 * ‖f‖) :=
    mul_le_mul_of_nonneg_left hR' η.gradient_bound_nonneg
  calc
    _ ≤ |h|⁻¹ * (K * ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (h • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖) :=
      mul_le_mul_of_nonneg_left hM' (inv_nonneg.mpr (abs_nonneg h))
    _ ≤ |h|⁻¹ * (K * (2 * ‖f‖)) :=
      mul_le_mul_of_nonneg_left hKR (inv_nonneg.mpr (abs_nonneg h))
    _ = (2 * K / |h|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

/-- The cutoff-gradient quotient operator norm is bounded by its totalized
`L²` constant. -/
theorem norm_cutoffGradientSpatialDifferenceQuotientL2_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) :
    ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h‖ ≤
      2 * K / |h| := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (mul_nonneg (by norm_num) η.gradient_bound_nonneg) (abs_nonneg h))
  intro f
  exact norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le hΩ η j k h f

end HypoellipticAleksandrov.Parabolic.Dirichlet
