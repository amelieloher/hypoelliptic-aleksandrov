module

public import Mathlib.Analysis.Normed.Operator.Extend
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange

/-!
# Localized spatial difference-quotient energy-test operator on `H¹₀`

This module constructs the bounded extension of the literal localized
backward energy test and proves its canonical value-space pivot.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The quotient-safe unweighted restricted scalar `L²` difference quotient. -/
private noncomputable def unweightedSpatialDifferenceQuotientL2
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  let μ : Measure (PDE.Vec d) := volume
  let z : PDE.Vec d := s • PDE.basisVec k
  let T : PDE.Vec d → PDE.Vec d := fun y => y + z
  let hT : MeasurePreserving T μ μ := measurePreserving_add_right μ z
  let E : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.zeroExtendLinearIsometry (μ := μ) hΩ).toContinuousLinearMap
  let P : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  let R : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ μ (2 : ℝ≥0∞) Ω
  s⁻¹ • R.comp (P.comp E - E)

/-- The outer quotient has its canonical ambient zero-extension formula. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y =>
        (⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
            (y + s • PDE.basisVec k) -
          ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / s := by
  unfold unweightedSpatialDifferenceQuotientL2
  dsimp
  have hP :
      ⇑((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k)))
        ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          fun y : PDE.Vec d => y + s • PDE.basisVec k) := by
    change MeasureTheory.Lp.compMeasurePreserving
      (fun y : PDE.Vec d => y + s • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k)) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) =ᵐ[volume]
        (⇑((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) ∘
          fun y : PDE.Vec d => y + s • PDE.basisVec k)
    exact MeasureTheory.Lp.coeFn_compMeasurePreserving
      ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k))
  have hR := LpToLpRestrictCLM_coeFn ℝ Ω
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + s • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsub := MeasureTheory.Lp.coeFn_sub
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + s • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
    ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)
  have hsmul := MeasureTheory.Lp.coeFn_smul s⁻¹
    ((LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f))
  filter_upwards [hsmul, hR, hsub.restrict, hP.restrict] with y hsmul hR hsub hP
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hR, hsub]
  simp only [Pi.sub_apply]
  rw [hP]
  simp only [Function.comp_def, div_eq_mul_inv]
  ring

/-- A representative supported in the raw domain may replace the canonical
zero extension in the unweighted quotient, with no collar premise. -/
private theorem unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hgsupp : Function.support g ⊆ Ω) :
    ⇑(unweightedSpatialDifferenceQuotientL2 hΩ k s f) =ᵐ[PDE.volumeOn Ω]
      fun y => (g (y + s • PDE.basisVec k) - g y) / s := by
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ f
  have hfg' := ae_imp_of_ae_restrict hfg
  have hambient : ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) =ᵐ[volume] g := by
    filter_upwards [hzero, hfg'] with y hzero hfg
    rw [hzero]
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
      exact hfg hy
    · rw [Set.indicator_of_notMem hy]
      have hgzero : g y = 0 := by
        by_contra hgne
        exact hy (hgsupp hgne)
      exact hgzero.symm
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (s • PDE.basisVec k)).quasiMeasurePreserving.ae hambient
  have hambientOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y = g y :=
    (ae_restrict_iff' hΩ).mpr (hambient.mono fun _ hy _ => hy)
  have hshiftedOn : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω,
      ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
        (y + s • PDE.basisVec k) = g (y + s • PDE.basisVec k) :=
    (ae_restrict_iff' hΩ).mpr (hshifted.mono fun _ hy _ => hy)
  filter_upwards [unweightedSpatialDifferenceQuotientL2_apply_ae hΩ k s f,
    hambientOn, hshiftedOn] with y hq hambient hshifted
  rw [hq, hambient, hshifted]

private theorem sq_tsupport_subset
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    tsupport η.sq.toFun ⊆ tsupport η.toFun := by
  simpa only [PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two] using
    (tsupport_mul_subset_left (f := η.toFun) (g := η.toFun))

private theorem energyWeakTest_partialDeriv_eq_backwardSquare
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)
    (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) (y : PDE.Vec d) :
    PDE.WeakTestFunction.partialDeriv
      (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j y =
      ((localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j
          (y + (-h) • PDE.basisVec k) -
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j y) / h := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  have hψshift : DifferentiableAt ℝ
      (fun x : PDE.Vec d => ψ (x + (-h) • PDE.basisVec k)) y :=
    (ψ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hψ : DifferentiableAt ℝ (ψ : PDE.Vec d → ℝ) y :=
    ψ.contDiff.contDiffAt.differentiableAt (by simp)
  let q : PDE.Vec d → ℝ := fun x =>
    ψ (x + (-h) • PDE.basisVec k) - ψ x
  have hq : DifferentiableAt ℝ q y := hψshift.sub hψ
  have hrewrite : localizedSpatialDifferenceQuotientEnergyTest η k h φ =
      fun x : PDE.Vec d => (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h := by
    funext x
    dsimp only [ψ]
    simp only [localizedSpatialDifferenceQuotientEnergyTest_apply,
      localizedSpatialDifferenceQuotient_apply,
      localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two]
    rw [sub_eq_add_neg, neg_smul]
    ring
  unfold PDE.WeakTestFunction.partialDeriv localizedSpatialDifferenceQuotientEnergyWeakTest
  change (fderiv ℝ (localizedSpatialDifferenceQuotientEnergyTest η k h φ) y)
      (PDE.basisVec j) = _
  rw [hrewrite]
  have hquotient : (fun x : PDE.Vec d =>
      (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h) = fun x => h⁻¹ • q x := by
    funext x
    simp only [q, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hquotient, fderiv_fun_const_smul hq h⁻¹]
  have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
      ψ.partialDeriv j (y + (-h) • PDE.basisVec k) - ψ.partialDeriv j y := by
    dsimp only [q]
    rw [fderiv_fun_sub hψshift hψ, fderiv_comp_add_right]
    rfl
  rw [ContinuousLinearMap.smul_apply, hqderiv]
  simp only [PDE.WeakTestFunction.partialDeriv, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The unweighted outer quotient has the totalized scalar `L²` bound. -/
private theorem norm_unweightedSpatialDifferenceQuotientL2_apply_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : MeasurableSet Ω) (k : Fin d) (s : ℝ)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖unweightedSpatialDifferenceQuotientL2 hΩ k s f‖ ≤ (2 / |s|) * ‖f‖ := by
  by_cases hs : s = 0
  · subst s
    simp [unweightedSpatialDifferenceQuotientL2]
  unfold unweightedSpatialDifferenceQuotientL2
  dsimp
  have hR : ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
      ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ ≤
      ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
        (fun y : PDE.Vec d => y + s • PDE.basisVec k)
        (measurePreserving_add_right (volume : Measure (PDE.Vec d))
          (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
        (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ :=
    norm_Lp_toLp_restrict_le Ω _
  have hD : ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
      (fun y : PDE.Vec d => y + s • PDE.basisVec k)
      (measurePreserving_add_right (volume : Measure (PDE.Vec d))
        (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
      (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ ≤ 2 * ‖f‖ := by
    calc
      _ ≤ ‖(MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + s • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ +
          ‖(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by
        rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
        ring
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |s|⁻¹ * ‖(LpToLpRestrictCLM (PDE.Vec d) ℝ ℝ volume 2 Ω)
        ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
          (fun y : PDE.Vec d => y + s • PDE.basisVec k)
          (measurePreserving_add_right (volume : Measure (PDE.Vec d))
            (s • PDE.basisVec k))) ((MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f) -
          (MeasureTheory.Lp.zeroExtendLinearIsometry hΩ) f)‖ := by rfl
    _ ≤ |s|⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left (hR.trans hD) (inv_nonneg.mpr (abs_nonneg s))
    _ = (2 / |s|) * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

/-- The literal smooth B core is linear before any completion argument. -/
noncomputable def energyTestSmoothCoreLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ where
  toFun φ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest,
      PDE.WeakTestFunction.add_toFun, Pi.add_def] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_add η k h
        (φ : PDE.Vec d → ℝ) (ψ : PDE.Vec d → ℝ)) y
  map_smul' c φ := by
    rw [← map_smul]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest, PDE.WeakTestFunction.smul_toFun,
      Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_smul c η k h
        (φ : PDE.Vec d → ℝ)) y

/-- The quotient-safe scalar receiver dictated by the literal B test. -/
private noncomputable def energyTestValueReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
      (valueCLM hΩ))

/-- Each B gradient coordinate has the forced outer-quotient receiver. -/
private noncomputable def energyTestGradientReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (-1 : ℝ) • (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)).comp
    ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
        ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)))

private noncomputable def energyTestGradientVectorReceiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun j => energyTestGradientReceiver hΩ η j k h

private theorem energyTestSmoothCore_value_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestValueReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  rw [hcore, hinput]
  change valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)) =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
  apply MeasureTheory.Lp.ext
  have hleft := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)
  have hinputAE := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hsqshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.sq.toFun) Ω := fun y hy => hηshift (sq_tsupport_subset η hy)
  have hA := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η.sq k h
    (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))
    φ hinputAE hsqshift
  have hAsupp : Function.support (localizedSpatialDifferenceQuotient η.sq k h φ) ⊆ Ω := by
    intro y hy
    exact hηΩ (sq_tsupport_subset η
      (tsupport_localizedSpatialDifferenceQuotient_subset η.sq k h φ
        (subset_tsupport _ hy)))
  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h)
    (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
      (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
    (localizedSpatialDifferenceQuotient η.sq k h φ) hA hAsupp
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))))
  filter_upwards [hleft, houter, hsmul] with y hleft houter hsmul
  rw [hleft, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter]
  change localizedSpatialDifferenceQuotientEnergyTest η k h φ y = _
  simp only [
    localizedSpatialDifferenceQuotientEnergyTest_apply,
    localizedSpatialDifferenceQuotient_apply,
    PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two]
  rw [sub_eq_add_neg, neg_smul]
  ring

private theorem energyTestSmoothCore_gradientCoord_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ)) =
      energyTestGradientReceiver hΩ η j k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  let F : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)) +
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
  have hcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
    apply Subtype.ext
    rfl
  have hinput : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hsqshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.sq.toFun) Ω := fun y hy => hηshift (sq_tsupport_subset η hy)
  have hcoord : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) = F := by
    dsimp only [F, ψ]
    exact localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
      hΩ η.sq k h φ ((sq_tsupport_subset η).trans hηΩ) hsqshift j
  rw [hcore, hinput]
  change PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift))) =
    (-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) F
  apply MeasureTheory.Lp.ext
  have hleftCoord := PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
    (gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)))
  have hleftJet := ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j
  have hinnerAE : ⇑F =ᵐ[PDE.volumeOn Ω] fun y => ψ.partialDeriv j y := by
    rw [← hcoord]
    exact (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))).trans
      (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ j)
  have hψsupport : Function.support (fun y => ψ.partialDeriv j y) ⊆ Ω := by
    intro y hy
    apply ψ.tsupport_subset
    by_contra hynot
    apply hy
    unfold PDE.WeakTestFunction.partialDeriv
    change (fderiv ℝ ψ.toFun y) (PDE.basisVec j) = 0
    rw [fderiv_of_notMem_tsupport ℝ hynot]
    exact ContinuousLinearMap.zero_apply _
  have houter := unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet k (-h) F (fun y => ψ.partialDeriv j y) hinnerAE hψsupport
  have hsmul := MeasureTheory.Lp.coeFn_smul (-1 : ℝ)
    (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) F)
  filter_upwards [hleftCoord, hleftJet, houter, hsmul] with y hleftCoord hleftJet houter hsmul
  rw [hleftCoord, hleftJet, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [houter]
  have hraw := energyWeakTest_partialDeriv_eq_backwardSquare
    η k h φ hηΩ hηshift j y
  dsimp only [ψ] at hraw ⊢
  rw [hraw]
  ring

private theorem energyTestSmoothCore_gradient_eq_receiver
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
      energyTestGradientVectorReceiver hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let L : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun j =>
    energyTestGradientReceiver hΩ η j k h
  have hcoord (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ)) =
      L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
    dsimp only [L]
    exact energyTestSmoothCore_gradientCoord_eq_receiver
      hΩ η j k h φ hηΩ hηshift
  change gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) =
    PDE.hilbertVectorLpAssemble L
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  apply MeasureTheory.Lp.ext
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ) y j =
        L j (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) y := by
    apply ae_all_iff.mpr
    intro j
    have hleft := PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ))
    filter_upwards [hleft] with y hleft
    exact hleft.symm.trans (congrArg (fun z : PDE.ScalarLp Ω (2 : ℝ≥0∞) => z y)
      (hcoord j))
  have hassemble := PDE.hilbertVectorLpAssemble_apply_ae L
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  filter_upwards [hcoords, hassemble] with y hcoords hassemble
  rw [hassemble]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
  ext j
  simpa only [PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv,
    WithLp.ofLp_toLp] using hcoords j

private theorem norm_hilbertVectorLpCoord_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (j : Fin d)
    (G : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) :
    ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ ≤ ‖G‖ := by
  rw [PDE.hilbertVectorLpCoord]
  calc
    ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).compLpL
        (2 : ℝ≥0∞) (PDE.volumeOn Ω) G‖ ≤
        ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j‖ * ‖G‖ := by
          exact ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖G‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa only [ContinuousLinearMap.coe_coe, Function.comp_def, PiLp.proj_apply, one_mul] using
        PiLp.norm_apply_le x j
    _ = ‖G‖ := one_mul _

private theorem norm_energyTestValueReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestValueReceiver hΩ η k h u‖ ≤ (4 / |h| ^ 2) * ‖u‖ := by
  have hvalue : ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
    let z : PDE.H1HilbertAmbient Ω := (u : PDE.H1HilbertGraph Ω).1
    change ‖z.fst‖ ≤ ‖z‖
    exact WithLp.norm_fst_le _ z
  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ u))‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
          (valueCLM hΩ u))‖ := by simp
    _ ≤ (2 / |-h|) * ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
        (valueCLM hΩ u)‖ := norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
    _ ≤ (2 / |h|) * ((2 / |h|) * ‖valueCLM hΩ u‖) := by
      rw [abs_neg]
      exact mul_le_mul_of_nonneg_left
        (norm_localizedSpatialDifferenceQuotientL2_apply_le
          hΩ.measurableSet η.sq k h (valueCLM hΩ u))
        (div_nonneg (by norm_num) (abs_nonneg h))
    _ ≤ (2 / |h|) * ((2 / |h|) * ‖u‖) := by
      gcongr
    _ = (4 / |h| ^ 2) * ‖u‖ := by ring

private theorem norm_energyTestGradientReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientReceiver hΩ η j k h u‖ ≤
      (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  have hvalue : ‖valueCLM hΩ u‖ ≤ ‖u‖ := by
    let z : PDE.H1HilbertAmbient Ω := (u : PDE.H1HilbertGraph Ω).1
    change ‖z.fst‖ ≤ ‖z‖
    exact WithLp.norm_fst_le _ z
  have hgradient : ‖gradientCLM hΩ u‖ ≤ ‖u‖ := by
    let z : PDE.H1HilbertAmbient Ω := (u : PDE.H1HilbertGraph Ω).1
    change ‖z.snd‖ ≤ ‖z‖
    exact WithLp.norm_snd_le _ z
  have hfirst : ‖(cutoffGradientSpatialDifferenceQuotientL2
      hΩ.measurableSet η.sq j k h).comp (valueCLM hΩ) u‖ ≤
      (4 * K / |h|) * ‖valueCLM hΩ u‖ := by
    change ‖cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h
      (valueCLM hΩ u)‖ ≤ _
    calc
      _ ≤ (2 * (2 * K) / |h|) * ‖valueCLM hΩ u‖ :=
        norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
          hΩ.measurableSet η.sq j k h (valueCLM hΩ u)
      _ = (4 * K / |h|) * ‖valueCLM hΩ u‖ := by ring
  have hsecond : ‖(localizedSpatialDifferenceQuotientL2
      hΩ.measurableSet η.sq k h).comp
      ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u‖ ≤
      (2 / |h|) * ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ u)‖ := by
    change ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))‖ ≤ _
    exact norm_localizedSpatialDifferenceQuotientL2_apply_le
      hΩ.measurableSet η.sq k h
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))
  change ‖(-1 : ℝ) • unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
      ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
          (valueCLM hΩ) u +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u)‖ ≤ _
  calc
    _ = ‖unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
        ((cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq j k h).comp
            (valueCLM hΩ) u +
          (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
            ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u)‖ := by
      rw [map_add]
      simp only [neg_one_smul]
      exact norm_neg _
    _ ≤ (2 / |-h|) * ‖(cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η.sq j k h).comp (valueCLM hΩ) u +
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η.sq k h).comp
          ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u‖ :=
      norm_unweightedSpatialDifferenceQuotientL2_apply_le _ _ _ _
    _ ≤ (2 / |h|) * ((4 * K / |h|) * ‖valueCLM hΩ u‖ +
        (2 / |h|) * ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ u)‖) := by
      rw [abs_neg]
      apply mul_le_mul_of_nonneg_left
      · exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
      · exact div_nonneg (by norm_num) (abs_nonneg h)
    _ ≤ (2 / |h|) * ((4 * K / |h|) * ‖u‖ + (2 / |h|) * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left hvalue
          exact div_nonneg (mul_nonneg (by norm_num) η.gradient_bound_nonneg) (abs_nonneg h)
        · apply mul_le_mul_of_nonneg_left
            ((norm_hilbertVectorLpCoord_le j (gradientCLM hΩ u)).trans hgradient)
          exact div_nonneg (by norm_num) (abs_nonneg h)
      · exact div_nonneg (by norm_num) (abs_nonneg h)
    _ = (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by ring

private theorem norm_energyTestGradientVectorReceiver_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u : H10HilbertGraph hΩ) :
    ‖energyTestGradientVectorReceiver hΩ η k h u‖ ≤
      (d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
  let L : Fin d → H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun j =>
    energyTestGradientReceiver hΩ η j k h
  change ‖PDE.hilbertVectorLpAssemble L u‖ ≤ _
  calc
    _ ≤ ∑ j, ‖L j u‖ := PDE.norm_hilbertVectorLpAssemble_apply_le L u
    _ ≤ ∑ _ : Fin d, (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_energyTestGradientReceiver_apply_le hΩ η j k h u
    _ = (d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2) * ‖u‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem norm_h10HilbertGraph_le_value_add_gradient
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : H10HilbertGraph hΩ) :
    ‖u‖ ≤ ‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖u‖ ^ 2 = ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 :=
      norm_sq_h10HilbertGraph hΩ u
    _ ≤ ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 +
        2 * (‖valueCLM hΩ u‖ * ‖gradientCLM hΩ u‖) := by
      apply le_add_of_nonneg_right
      exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖) ^ 2 := by ring

private theorem norm_energyTestSmoothCoreLinearMap_apply_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤
      (4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2) *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  let x : H10HilbertGraph hΩ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let q : H10HilbertGraph hΩ := energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ
  have hvalue : valueCLM hΩ q = energyTestValueReceiver hΩ η k h x := by
    simpa only [q, x] using energyTestSmoothCore_value_eq_receiver
      hΩ η k h φ hηΩ hηshift
  have hgradient : gradientCLM hΩ q = energyTestGradientVectorReceiver hΩ η k h x := by
    simpa only [q, x] using energyTestSmoothCore_gradient_eq_receiver
      hΩ η k h φ hηΩ hηshift
  calc
    ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ = ‖q‖ := rfl
    _ ≤ ‖valueCLM hΩ q‖ + ‖gradientCLM hΩ q‖ :=
      norm_h10HilbertGraph_le_value_add_gradient hΩ q
    _ = ‖energyTestValueReceiver hΩ η k h x‖ +
        ‖energyTestGradientVectorReceiver hΩ η k h x‖ := by rw [hvalue, hgradient]
    _ ≤ (4 / |h| ^ 2) * ‖x‖ +
        ((d : ℝ) * (4 * (2 * K + 1) / |h| ^ 2)) * ‖x‖ :=
      add_le_add (norm_energyTestValueReceiver_apply_le hΩ η k h x)
        (norm_energyTestGradientVectorReceiver_apply_le hΩ η k h x)
    _ = (4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2) * ‖x‖ := by ring

private theorem exists_energyTestSmoothCoreLinearMap_bound
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  refine ⟨4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2, ?_⟩
  intro φ
  exact norm_energyTestSmoothCoreLinearMap_apply_le hΩ η k h φ hηΩ hηshift

private theorem energyTest_bound_nonneg
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (h : ℝ) :
    0 ≤ 4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2 := by
  have hK : 0 ≤ K := η.gradient_bound_nonneg
  positivity

/-- The internal bounded extension of the smooth localized energy test. -/
noncomputable def energyTestH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift).extendOfNorm
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

private theorem energyTestH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ := by
  unfold energyTestH10CLM
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_energyTestSmoothCoreLinearMap_bound hΩ η k h hηΩ hηshift) φ

private theorem norm_energyTestH10CLM_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖energyTestH10CLM hΩ η k h hηΩ hηshift‖ ≤
      4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2 := by
  unfold energyTestH10CLM
  apply LinearMap.opNorm_extendOfNorm_le
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (energyTest_bound_nonneg η h)
  intro φ
  exact norm_energyTestSmoothCoreLinearMap_apply_le hΩ η k h φ hηΩ hηshift

private theorem inner_scalarLp_eq_integral_mul_of_ae_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (F G : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (f g : PDE.Vec d → ℝ)
    (hF : ⇑F =ᵐ[PDE.volumeOn Ω] f) (hG : ⇑G =ᵐ[PDE.volumeOn Ω] g) :
    inner ℝ F G = ∫ y, f y * g y ∂PDE.volumeOn Ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF, hG] with y hF hG
  rw [hF, hG]
  simp [mul_comm]

private theorem inner_value_energyTestSmoothCore_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ
      (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
      (valueCLM hΩ (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift ψ)) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
  have hφcore : smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hψcore : energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift ψ =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift) := by
    apply Subtype.ext
    rfl
  rw [hφcore, hψcore]
  have hφ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hψ := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift)
  have hAφ := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))
    φ hφ hηshift
  have hAψbase := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ
  have hAψ := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))
    ψ hAψbase hηshift
  calc
    _ = ∫ y, φ y * localizedSpatialDifferenceQuotientEnergyTest η k h ψ y
        ∂PDE.volumeOn Ω := by
      apply inner_scalarLp_eq_integral_mul_of_ae_eq
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift)))
        φ (localizedSpatialDifferenceQuotientEnergyTest η k h ψ) hφ
      exact hψ
    _ = ∫ y, localizedSpatialDifferenceQuotient η k h φ y *
        localizedSpatialDifferenceQuotient η k h ψ y ∂PDE.volumeOn Ω := by
      change (∫ y in Ω, φ y * localizedSpatialDifferenceQuotientEnergyTest η k h ψ y
        ∂volume) = _
      rw [setIntegral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
        η k h φ ψ φ.contDiff.continuous ψ.contDiff.continuous hηΩ hηshift]
    _ = _ := (inner_scalarLp_eq_integral_mul_of_ae_eq
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)))
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)))
      (localizedSpatialDifferenceQuotient η k h φ)
      (localizedSpatialDifferenceQuotient η k h ψ) hAφ hAψ).symm

private theorem value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := by
  have h := congrArg (fun M : H10HilbertGraph hΩ →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) => M
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
    (valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
  simpa only [ContinuousLinearMap.comp_apply] using h

private noncomputable def energyTestSmoothLeftPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))).comp
      ((valueCLM hΩ).comp (energyTestH10CLM hΩ η k h hηΩ hηshift))

private noncomputable def localizedSmoothLeftPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift))

private theorem energyTestSmoothLeftPairCLM_apply
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (v : H10HilbertGraph hΩ) :
    energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift v =
      Inner.inner ℝ
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
        (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) := by
  rfl

private theorem localizedSmoothLeftPairCLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ ψ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ) =
      Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
  change Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) = _
  calc
    _ = Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))) := by
      exact congrArg (fun z => Inner.inner ℝ z
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))))
        (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
          hΩ η k h φ hηΩ hηshift)
    _ = _ := by
      exact congrArg (fun z => Inner.inner ℝ
        (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))) z)
        (value_localizedSpatialDifferenceQuotientH10CLM_apply_smooth
          hΩ η k h ψ hηΩ hηshift)

private theorem energyTestSmoothLeftPairCLM_eq_localizedSmoothLeftPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift =
      localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift := by
  apply ContinuousLinearMap.ext
  exact fun w => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      (energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift).continuous
      (localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift).continuous (by
      funext ψ
      change energyTestSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ) =
        localizedSmoothLeftPairCLM hΩ η k h φ hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ)
      rw [energyTestSmoothLeftPairCLM_apply]
      rw [energyTestH10CLM_apply_smooth hΩ η k h ψ hηΩ hηshift]
      rw [localizedSmoothLeftPairCLM_apply_smooth]
      exact inner_value_energyTestSmoothCore_eq hΩ η k h φ ψ hηΩ hηshift)) w

private theorem inner_value_energyTestH10CLM_eq_of_smooth_left
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
      (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) =
      Inner.inner ℝ (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := by
  exact congrArg (fun M : H10HilbertGraph hΩ →L[ℝ] ℝ => M v)
    (energyTestSmoothLeftPairCLM_eq_localizedSmoothLeftPairCLM
      hΩ η k h φ hηΩ hηshift)

private noncomputable def energyTestFixedRightPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))).comp
    (valueCLM hΩ)

private noncomputable def localizedFixedRightPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))).comp
      ((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))

private theorem energyTestFixedRightPairCLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      Inner.inner ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := by
  rfl

private theorem localizedFixedRightPairCLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      Inner.inner ℝ (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))) := by
  rfl

private theorem energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift =
      localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift := by
  apply ContinuousLinearMap.ext
  exact fun u => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      (energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous
      (localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift).continuous (by
      funext φ
      change energyTestFixedRightPairCLM hΩ η k h v hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
        localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
      rw [energyTestFixedRightPairCLM_apply_smooth]
      rw [localizedFixedRightPairCLM_apply_smooth]
      calc
        _ = Inner.inner ℝ
            (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
            (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) :=
          real_inner_comm _ _
        _ = Inner.inner ℝ (valueCLM hΩ
            (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
              (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)))
            (valueCLM hΩ
              (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) :=
          inner_value_energyTestH10CLM_eq_of_smooth_left hΩ η k h φ v hηΩ hηshift
        _ = _ := real_inner_comm _ _)) u

private theorem inner_value_energyTestH10CLM_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := by
  calc
    _ = Inner.inner ℝ (valueCLM hΩ (energyTestH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ u) := real_inner_comm _ _
    _ = Inner.inner ℝ (valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v))
        (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u)) :=
      congrArg (fun M : H10HilbertGraph hΩ →L[ℝ] ℝ => M u)
        (energyTestFixedRightPairCLM_eq_localizedFixedRightPairCLM hΩ η k h v hηΩ hηshift)
    _ = _ := real_inner_comm _ _

/-- The bounded H10 extension of the localized spatial energy test. -/
noncomputable def localizedSpatialDifferenceQuotientEnergyTestH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  energyTestH10CLM hΩ η k h hηΩ hηshift

/-- The energy-test extension agrees with the literal bundled smooth core. -/
theorem localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
  change energyTestH10CLM hΩ η k h hηΩ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) = _
  rw [energyTestH10CLM_apply_smooth hΩ η k h φ hηΩ hηshift]
  rfl

/-- The energy-test value pairing is the localized quotient inner product. -/
theorem inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := by
  exact inner_value_energyTestH10CLM_eq hΩ η k h u v hηΩ hηshift

/-- The totalized operator-norm bound for the localized energy test. -/
theorem norm_localizedSpatialDifferenceQuotientEnergyTestH10CLM_le
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift‖ ≤
      4 * (1 + (d : ℝ) * (2 * K + 1)) / |h| ^ 2 := by
  exact norm_energyTestH10CLM_le hΩ η k h hηΩ hηshift

end HypoellipticAleksandrov.Parabolic.Dirichlet
