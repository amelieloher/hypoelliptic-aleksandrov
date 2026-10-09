module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialSegmentSafeOpen
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak derivatives paired with signed spatial difference quotients

This module identifies the pairing of a signed spatial difference quotient
with a smooth compactly supported test as the average of pairings with the
selected weak velocity derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal Topology

private theorem spatialShift_segment_formula
    {d : ℕ} (k : Fin d) (h t : ℝ) (z : TimeVelocity d) :
    spatialShift k (t * h) z =
      z + t • (spatialShift k h z - z) := by
  rcases z with ⟨r, y⟩
  simp only [spatialShift_apply, Prod.mk_add_mk, add_zero, Prod.mk_sub_mk,
    sub_self, Prod.smul_mk, smul_zero, Prod.mk.injEq, true_and]
  module

private theorem backward_spatialDifferenceQuotient_eq_intervalIntegral
    {d : ℕ} (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : TimeVelocity d) :
    spatialDifferenceQuotient k (-h) φ z =
      ∫ t in (0 : ℝ)..1,
        velocityGradient φ (spatialShift k (-(t * h)) z) k := by
  let F : ℝ → ℝ := fun t => φ (spatialShift k (-(t * h)) z)
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hFdiff : Differentiable ℝ F := by
    have hline : Differentiable ℝ (fun t : ℝ => spatialShift k (-(t * h)) z) := by
      dsimp only [spatialShift]
      fun_prop
    exact hφdiff.fun_comp hline
  have hFderiv : ∀ t : ℝ,
      deriv F t = -h * velocityGradient φ (spatialShift k (-(t * h)) z) k := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => spatialShift k (-(s * h)) z)
        ((0, -h • PDE.basisVec k) : TimeVelocity d) t := by
      convert (((hasDerivAt_id t).mul_const h).neg.smul_const
        ((0, PDE.basisVec k) : TimeVelocity d)).const_add z using 1 <;>
        simp [spatialShift]
    rw [show deriv F t = (fderiv ℝ φ (spatialShift k (-(t * h)) z))
        ((0, -h • PDE.basisVec k) : TimeVelocity d) by
      exact ((hφdiff _).hasFDerivAt.comp_hasDerivAt t hline).deriv]
    change (fderiv ℝ φ (spatialShift k (-(t * h)) z))
        ((0, -h • PDE.basisVec k) : TimeVelocity d) = _
    rw [show ((0, -h • PDE.basisVec k) : TimeVelocity d) =
        -h • ((0, PDE.basisVec k) : TimeVelocity d) by simp]
    rw [map_smul]
    rfl
  have hDcont : Continuous (fun t : ℝ =>
      velocityGradient φ (spatialShift k (-(t * h)) z) k) := by
    unfold velocityGradient
    apply ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    dsimp only [spatialShift]
    fun_prop
  have hderivInt : IntervalIntegrable (deriv F) volume 0 1 := by
    rw [show deriv F = fun t =>
        -h * velocityGradient φ (spatialShift k (-(t * h)) z) k by
      funext t
      exact hFderiv t]
    exact (continuous_const.mul hDcont).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (f := F) (a := (0 : ℝ)) (b := 1) (fun t _ => hFdiff t)
    hderivInt
  rw [show (∫ t in (0 : ℝ)..1, deriv F t) =
      -h * ∫ t in (0 : ℝ)..1,
        velocityGradient φ (spatialShift k (-(t * h)) z) k by
    simp_rw [hFderiv, intervalIntegral.integral_const_mul]]
    at hFTC
  simp only [F, one_mul, neg_mul, zero_mul, neg_zero,
    spatialShift_zero, id_eq] at hFTC
  rw [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  apply (div_eq_iff (neg_ne_zero.mpr hh)).2
  linarith

private theorem translated_test_tsupport_subset
    {d : ℕ} (U : Set (TimeVelocity d)) (k : Fin d) (h t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (φ : TimeVelocity d → ℝ)
    (hφsafe : tsupport φ ⊆ spatialSegmentSafeSet U k h) :
    tsupport (fun z => φ (spatialShift k (-(t * h)) z)) ⊆ U := by
  intro z hz
  have hz' : spatialShift k (-(t * h)) z ∈ tsupport φ := by
    change z ∈ tsupport (spatialTranslate k (-(t * h)) φ) at hz
    rwa [mem_tsupport_spatialTranslate_iff] at hz
  have hsafe := hφsafe hz'
  rw [mem_spatialSegmentSafeSet_iff,
    segment_eq_image' ℝ (spatialShift k (-(t * h)) z)
      (spatialShift k h (spatialShift k (-(t * h)) z))] at hsafe
  apply hsafe
  refine ⟨t, ht, ?_⟩
  change spatialShift k (-(t * h)) z +
      t • (spatialShift k h (spatialShift k (-(t * h)) z) -
        spatialShift k (-(t * h)) z) = z
  rw [← spatialShift_segment_formula]
  change (spatialShift k (t * h) ∘ spatialShift k (-(t * h))) z = z
  rw [spatialShift_comp]
  simp

private theorem integrable_joint_shifted_mul
    {d : ℕ} (U : Set (TimeVelocity d)) (k : Fin d) (h : ℝ)
    (u φ : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ) :
    Integrable (Function.uncurry fun t z =>
      u z * velocityGradient φ (spatialShift k (-(t * h)) z) k)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict U : Measure (TimeVelocity d))) := by
  let μt : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let μU : Measure (TimeVelocity d) := volume.restrict U
  let shear : ℝ × TimeVelocity d → ℝ × TimeVelocity d :=
    fun p => (p.1, spatialShift k (-(p.1 * h)) p.2)
  have hshear : MeasurePreserving shear
      (μt.prod (volume : Measure (TimeVelocity d)))
      (μt.prod (volume : Measure (TimeVelocity d))) := by
    refine MeasurePreserving.skew_product (g := fun t z => spatialShift k (-(t * h)) z)
      (MeasurePreserving.id _) ?_ ?_
    · dsimp [spatialShift]
      fun_prop
    · filter_upwards [] with t
      exact (spatialShift_measurePreserving k (-(t * h))).map_eq
  have hgrad : MemLp (fun z : TimeVelocity d => velocityGradient φ z k)
      (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) := by
    exact ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφcompact.fderiv_apply ℝ ((0, PDE.basisVec k) : TimeVelocity d))
  have hgradProd : MemLp (fun p : ℝ × TimeVelocity d =>
      velocityGradient φ p.2 k) (2 : ℝ≥0∞)
      (μt.prod (volume : Measure (TimeVelocity d))) := hgrad.comp_snd μt
  have hgradShift : MemLp (fun p : ℝ × TimeVelocity d =>
      velocityGradient φ (spatialShift k (-(p.1 * h)) p.2) k)
      (2 : ℝ≥0∞) (μt.prod (volume : Measure (TimeVelocity d))) := by
    simpa only [Function.comp_def, shear, Function.comp_def] using
      hgradProd.comp_measurePreserving hshear
  have hprodRestrict : μt.prod μU =
      (μt.prod (volume : Measure (TimeVelocity d))).restrict (univ ×ˢ U) := by
    calc
      μt.prod μU = (μt.restrict univ).prod
          ((volume : Measure (TimeVelocity d)).restrict U) := by simp [μU]
      _ = (μt.prod (volume : Measure (TimeVelocity d))).restrict (univ ×ˢ U) :=
        Measure.prod_restrict univ U
  have hgradShiftU : MemLp (fun p : ℝ × TimeVelocity d =>
      velocityGradient φ (spatialShift k (-(p.1 * h)) p.2) k)
      (2 : ℝ≥0∞) (μt.prod μU) := by
    rw [hprodRestrict]
    exact hgradShift.mono_measure Measure.restrict_le_self
  have huProd : MemLp (fun p : ℝ × TimeVelocity d => u p.2)
      (2 : ℝ≥0∞) (μt.prod μU) := hu.comp_snd μt
  simpa only [Function.comp_def, μt, μU, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Function.uncurry_def, Pi.mul_def, timeVelocityVolumeOn] using
    huProd.integrable_mul hgradShiftU

private theorem sqNorm_integral_eq_norm_sq_toLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (F : α → E) (hF : MemLp F (2 : ℝ≥0∞) μ) :
    ∫ x, ‖F x‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hF.coeFn_toLp,
    hF.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

private theorem integrable_joint_shifted_test_mul
    {d : ℕ} (U : Set (TimeVelocity d)) (k : Fin d) (h : ℝ)
    (g φ : TimeVelocity d → ℝ)
    (hg : ParabolicMemLpOn U (2 : ℝ≥0∞) g)
    (hφmem : MemLp φ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable (Function.uncurry fun t z =>
      g z * φ (spatialShift k (-(t * h)) z))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict U : Measure (TimeVelocity d))) := by
  let μt : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let shear : ℝ × TimeVelocity d → ℝ × TimeVelocity d :=
    fun p => (p.1, spatialShift k (-(p.1 * h)) p.2)
  have hshear : MeasurePreserving shear (μt.prod volume) (μt.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun t z => spatialShift k (-(t * h)) z)
      (MeasurePreserving.id _) ?_ ?_
    · dsimp [spatialShift]
      fun_prop
    · filter_upwards [] with t
      exact (spatialShift_measurePreserving k (-(t * h))).map_eq
  have hφshift : MemLp (fun p : ℝ × TimeVelocity d =>
      φ (spatialShift k (-(p.1 * h)) p.2)) (2 : ℝ≥0∞) (μt.prod volume) := by
    simpa only [Function.comp_def, shear, Function.comp_def] using
      (hφmem.comp_snd μt).comp_measurePreserving hshear
  have hprod : μt.prod (volume.restrict U : Measure (TimeVelocity d)) =
      (μt.prod volume).restrict (univ ×ˢ U) := by
    calc
      μt.prod (volume.restrict U : Measure (TimeVelocity d)) =
          (μt.restrict univ).prod (volume.restrict U) := by simp
      _ = (μt.prod volume).restrict (univ ×ˢ U) := Measure.prod_restrict univ U
  have hφshiftU : MemLp (fun p : ℝ × TimeVelocity d =>
      φ (spatialShift k (-(p.1 * h)) p.2)) (2 : ℝ≥0∞)
      (μt.prod (volume.restrict U)) := by
    rw [hprod]
    exact hφshift.mono_measure Measure.restrict_le_self
  have hgProd := hg.comp_snd μt
  simpa only [Function.comp_def, μt, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Function.uncurry_def, Pi.mul_def, timeVelocityVolumeOn] using
    hgProd.integrable_mul hφshiftU

/-- Pairing a signed spatial difference quotient with a smooth compactly
supported test equals the average pairing with the selected weak derivative. -/
theorem HasWeakVelocityPartialDerivOn.setIntegral_spatialDifferenceQuotient_mul_eq_intervalIntegral
    {d : ℕ} (U : Set (TimeVelocity d))
    (k : Fin d) (h : ℝ) (u g φ : TimeVelocity d → ℝ)
    (hh : h ≠ 0)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (hg : ParabolicMemLpOn U (2 : ℝ≥0∞) g)
    (hweak : HasWeakVelocityPartialDerivOn U k u g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (hφsafe : tsupport φ ⊆ spatialSegmentSafeSet U k h) :
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z
      ∂(volume : Measure (TimeVelocity d))) =
      ∫ t in (0 : ℝ)..1,
        ∫ z in U, g z * φ (spatialShift k (-(t * h)) z)
          ∂(volume : Measure (TimeVelocity d)) := by
  have hφU : tsupport φ ⊆ U := by
    intro z hz
    have hs := hφsafe hz
    rw [mem_spatialSegmentSafeSet_iff] at hs
    exact hs (left_mem_segment ℝ z (spatialShift k h z))
  have hφshift : MapsTo (spatialShift k h) (tsupport φ) U := by
    intro z hz
    have hs := hφsafe hz
    rw [mem_spatialSegmentSafeSet_iff] at hs
    exact hs (right_mem_segment ℝ z (spatialShift k h z))
  rw [setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
    U k h u φ hu hφ.continuous hφcompact hφU hφshift]
  have hjoint := integrable_joint_shifted_mul U k h u φ hu hφ hφcompact
  have hswap := intervalIntegral_integral_swap hjoint
  rw [show (∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z ∂volume) =
      ∫ z in U, ∫ t in (0 : ℝ)..1,
        u z * velocityGradient φ (spatialShift k (-(t * h)) z) k by
    apply integral_congr_ae
    filter_upwards with z
    rw [backward_spatialDifferenceQuotient_eq_intervalIntegral k h hh φ hφ,
      intervalIntegral.integral_const_mul]]
  rw [← hswap]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using ht
  have htestSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (HypoellipticAleksandrov.Parabolic.spatialTranslate k (-(t * h)) φ) :=
    ContDiff.spatialTranslate hφ
  have htestCompact : HasCompactSupport
      (HypoellipticAleksandrov.Parabolic.spatialTranslate k (-(t * h)) φ) :=
    HasCompactSupport.spatialTranslate hφcompact
  have htestSupport := translated_test_tsupport_subset U k h t ht' φ hφsafe
  have hw := hweak (HypoellipticAleksandrov.Parabolic.spatialTranslate k (-(t * h)) φ)
    htestSmooth htestCompact htestSupport
  simpa only [Function.comp_def, spatialTranslate_apply, velocityGradient_spatialTranslate,
    neg_neg] using
    congrArg Neg.neg hw

/-- The averaged weak-derivative identity obeys the sharp constant-one `L²`
Cauchy--Schwarz bound. -/
theorem HasWeakVelocityPartialDerivOn.abs_setIntegral_spatialDifferenceQuotient_mul_le
    {d : ℕ} (U : Set (TimeVelocity d))
    (k : Fin d) (h : ℝ) (u g φ : TimeVelocity d → ℝ)
    (hh : h ≠ 0)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (hg : ParabolicMemLpOn U (2 : ℝ≥0∞) g)
    (hweak : HasWeakVelocityPartialDerivOn U k u g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (hφsafe : tsupport φ ⊆ spatialSegmentSafeSet U k h) :
    |∫ z in U, spatialDifferenceQuotient k h u z * φ z
      ∂(volume : Measure (TimeVelocity d))| ≤
      ‖hg.toLp g‖ *
        ‖(hφ.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) (μ :=
          (volume : Measure (TimeVelocity d))) hφcompact).toLp φ‖ := by
  rw [hweak.setIntegral_spatialDifferenceQuotient_mul_eq_intervalIntegral
    U k h u g φ hh hu hg hφ hφcompact hφsafe]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
  let hφmem : MemLp φ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφcompact
  have hslice : ∀ t : ℝ,
      |∫ z in U, g z * φ (spatialShift k (-(t * h)) z) ∂volume| ≤
        ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by
    intro t
    let ψ : TimeVelocity d → ℝ := fun z => φ (spatialShift k (-(t * h)) z)
    have hψglobal : MemLp ψ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) := by
      change MemLp (φ ∘ spatialShift k (-(t * h))) (2 : ℝ≥0∞) volume
      exact hφmem.comp_measurePreserving (spatialShift_measurePreserving k (-(t * h)))
    have hψU : MemLp ψ (2 : ℝ≥0∞)
        (volume.restrict U : Measure (TimeVelocity d)) :=
      hψglobal.mono_measure Measure.restrict_le_self
    have hg' : MemLp g (ENNReal.ofReal (2 : ℝ))
        (volume.restrict U : Measure (TimeVelocity d)) := by
      simpa only [ParabolicMemLpOn, ENNReal.ofReal_ofNat] using
          hg
    calc
      |∫ z in U, g z * ψ z ∂volume| ≤ ∫ z in U, |g z| * |ψ z| ∂volume := by
        simpa only [Function.comp_def, Real.norm_eq_abs, norm_mul] using
          (norm_integral_le_integral_norm (μ := volume.restrict U)
            (fun z => g z * ψ z))
      _ ≤ (∫ z in U, |g z| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
          (∫ z in U, |ψ z| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
        simpa only [Function.comp_def, Real.norm_eq_abs] using
          (integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict U)
            (f := g) (g := ψ) Real.HolderConjugate.two_two hg'
            (by simpa only [ENNReal.ofReal_ofNat] using hψU))
      _ = ‖hg.toLp g‖ * ‖hψU.toLp ψ‖ := by
        have hgsq := sqNorm_integral_eq_norm_sq_toLp g hg
        have hψsq := sqNorm_integral_eq_norm_sq_toLp ψ hψU
        simp only [Real.norm_eq_abs] at hgsq hψsq
        have hgroot : (∫ z, |g z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^
            (1 / (2 : ℝ)) = ‖hg.toLp g‖ := by
          simp only [Real.rpow_two]
          rw [← Real.sqrt_eq_rpow, hgsq, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
        have hψroot : (∫ z, |ψ z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^
            (1 / (2 : ℝ)) = ‖hψU.toLp ψ‖ := by
          simp only [Real.rpow_two]
          rw [← Real.sqrt_eq_rpow, hψsq, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
        change ((∫ z, |g z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^ (1 / (2 : ℝ))) *
            ((∫ z, |ψ z| ^ (2 : ℝ) ∂timeVelocityVolumeOn U) ^ (1 / (2 : ℝ))) = _
        rw [hgroot, hψroot]
      _ ≤ ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by
        gcongr
        rw [Lp.norm_toLp, Lp.norm_toLp]
        refine ENNReal.toReal_mono (memLp_iff.mp hφmem).ne ?_
        calc
          eLpNorm ψ 2 (volume.restrict U) ≤ eLpNorm ψ 2 volume :=
            eLpNorm_mono_measure ψ Measure.restrict_le_self
          _ = eLpNorm φ 2 volume := by
            exact eLpNorm_comp_measurePreserving hφmem.aestronglyMeasurable
              (spatialShift_measurePreserving k (-(t * h)))
      _ = ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := rfl
  have hjoint := integrable_joint_shifted_test_mul U k h g φ hg hφmem
  have houter : IntervalIntegrable (fun t =>
      ∫ z in U, g z * φ (spatialShift k (-(t * h)) z) ∂volume) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).2
    simpa only [Function.comp_def, IntegrableOn, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Function.uncurry_def, Pi.mul_def, timeVelocityVolumeOn] using hjoint.integral_prod_left
  calc
    ∫ t in (0 : ℝ)..1,
        |∫ z in U, g z * φ (spatialShift k (-(t * h)) z) ∂volume| ≤
        ∫ _t in (0 : ℝ)..1, ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by
      exact intervalIntegral.integral_mono_on (by norm_num) houter.abs
        (intervalIntegrable_const)
        (fun t _ => hslice t)
    _ = ‖hg.toLp g‖ * ‖hφmem.toLp φ‖ := by simp

end HypoellipticAleksandrov.Parabolic
