module

public import PDEFoundation.Measure.SegmentDouble
public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth convex-domain Poincaré estimates

This file collects the bounded-domain integrability facts and analytic
estimates used before passing the diameter-only Poincaré inequality from
globally smooth functions to Sobolev representatives.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- A nonnegative real power of the Euclidean magnitude of a smooth classical
gradient is integrable on every bounded Sobolev-regular domain. -/
theorem integrableOn_vecEuclideanNorm_classicalGradient_rpow
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u)
    {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn
      (fun z =>
        vecEuclideanNorm (classicalGradient u z) ^ p)
      U volume := by
  have hgrad :
      Continuous (classicalGradient u) :=
    PDE.ContDiff.continuous_classicalGradient hu
  have hcont :
      Continuous
        (fun z =>
          vecEuclideanNorm (classicalGradient u z) ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp (continuous_vecEuclideanNorm.comp hgrad)
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  exact
    (hcont.continuousOn.integrableOn_compact
      hclosureCompact).mono_set subset_closure

/-- For a fixed point, the `p`th power of the smooth pairwise oscillation is
integrable on a bounded Sobolev-regular domain. -/
theorem integrableOn_abs_sub_rpow_of_contDiff
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u)
    {p : ℝ} (hp : 0 ≤ p) (x : Vec d) :
    IntegrableOn (fun y => |u x - u y| ^ p)
      U volume := by
  have huCont : Continuous u :=
    hu.continuous
  have hcont :
      Continuous (fun y => |u x - u y| ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp (continuous_const.sub huCont).abs
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  exact
    (hcont.continuousOn.integrableOn_compact
      hclosureCompact).mono_set subset_closure

/-- The smooth mean-subtracted `p`th power is integrable on a bounded
Sobolev-regular domain. -/
theorem integrableOn_abs_sub_integralAverage_rpow_of_contDiff
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u)
    {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn
      (fun x => |u x - integralAverage U u| ^ p)
      U volume := by
  have huCont : Continuous u :=
    hu.continuous
  have hcont :
      Continuous
        (fun x => |u x - integralAverage U u| ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp (huCont.sub continuous_const).abs
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  exact
    (hcont.continuousOn.integrableOn_compact
      hclosureCompact).mono_set subset_closure

/-- The `p`th power of pairwise smooth oscillation is integrable on the
product of a bounded Sobolev-regular domain with itself. -/
theorem integrableOn_prod_abs_sub_rpow_of_contDiff
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u)
    {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn
      (fun z : Vec d × Vec d =>
        |u z.1 - u z.2| ^ p)
      (U ×ˢ U) (volume.prod volume) := by
  have huCont : Continuous u :=
    hu.continuous
  have hcont :
      Continuous
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp
        ((huCont.comp continuous_fst).sub
          (huCont.comp continuous_snd)).abs
  have hclosureCompact :
      IsCompact (closure U ×ˢ closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure.prod
      hU.isBoundedDomain.isBounded.isCompact_closure
  have hprod :
      IntegrableOn
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        (closure U ×ˢ closure U)
        (volume.prod volume) :=
    hcont.continuousOn.integrableOn_compact
      hclosureCompact
  exact hprod.mono_set (Set.prod_mono subset_closure subset_closure)

/-- Integrated Jensen inequality comparing oscillation about the arithmetic
mean with the normalized pairwise oscillation. -/
theorem setIntegral_abs_sub_integralAverage_rpow_le
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    ∫ x in U, |u x - integralAverage U u| ^ p ∂volume ≤
      (volume U).toReal⁻¹ *
        ∫ x in U, ∫ y in U,
          |u x - u y| ^ p ∂volume ∂volume := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  have huInt :
      IntegrableOn u U volume := by
    have hclosureCompact : IsCompact (closure U) :=
      hU.isBoundedDomain.isBounded.isCompact_closure
    exact
      (hu.continuous.continuousOn.integrableOn_compact
        hclosureCompact).mono_set subset_closure
  have hleft :
      IntegrableOn
        (fun x => |u x - integralAverage U u| ^ p)
        U volume :=
    integrableOn_abs_sub_integralAverage_rpow_of_contDiff
      hU.isSobolevRegularDomain (hu.of_le (by simp)) hpNonneg
  have hpair :
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        ((volume.restrict U).prod
          (volume.restrict U)) := by
    simpa only [← Measure.prod_restrict, IntegrableOn] using
      integrableOn_prod_abs_sub_rpow_of_contDiff
        hU.isSobolevRegularDomain
        (hu.of_le (by simp)) hpNonneg
  have hinner :
      IntegrableOn
        (fun x => ∫ y in U, |u x - u y| ^ p ∂volume)
        U volume := by
    simpa only [IntegrableOn] using hpair.integral_prod_left
  have hright :
      IntegrableOn
        (fun x =>
          (volume U).toReal⁻¹ *
            ∫ y in U, |u x - u y| ^ p ∂volume)
        U volume :=
    hinner.const_mul (volume U).toReal⁻¹
  calc
    (∫ x in U,
        |u x - integralAverage U u| ^ p ∂volume) ≤
        ∫ x in U,
          (volume U).toReal⁻¹ *
            ∫ y in U, |u x - u y| ^ p ∂volume
          ∂volume := by
      refine setIntegral_mono_on
        hleft hright hU.measurableSet ?_
      intro x _hx
      have hJensen :=
        abs_sub_integralAverage_rpow_le_integral_abs_sub_rpow
          hp huInt hUPos hUTop x
          (integrableOn_abs_sub_rpow_of_contDiff
            hU.isSobolevRegularDomain
            (hu.of_le (by simp)) hpNonneg x)
      simpa only [normalizedVolumeOn,
        integral_smul_measure, ENNReal.toReal_inv,
        volumeOn] using! hJensen
    _ = (volume U).toReal⁻¹ *
        ∫ x in U, ∫ y in U,
          |u x - u y| ^ p ∂volume ∂volume := by
      rw [integral_const_mul]

/-- Smooth pairwise oscillation is controlled by the diameter and the
Euclidean gradient, with a constant independent of `p`. -/
theorem setIntegral_setIntegral_abs_sub_rpow_le
    {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ x in U, ∫ y in U,
        |u x - u y| ^ p ∂volume ∂volume) ≤
      D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume) := by
  have hpNonneg : 0 ≤ p :=
    zero_le_one.trans hp
  let g : Vec d → ℝ :=
    fun z =>
      vecEuclideanNorm (classicalGradient u z) ^ p
  let μU : Measure (Vec d) :=
    volumeOn U
  let μPair : Measure (Vec d × Vec d) :=
    μU.prod μU
  let F : ℝ → Vec d × Vec d → ℝ :=
    fun t z => g (segmentBlend z.1 t z.2)
  have hgradCont :
      Continuous (classicalGradient u) :=
    PDE.ContDiff.continuous_classicalGradient
      (hu.of_le (by norm_num) : ContDiff ℝ 1 u)
  have hgCont : Continuous g := by
    exact
      Real.continuous_rpow_const hpNonneg
        |>.comp (continuous_vecEuclideanNorm.comp hgradCont)
  have hgNonneg : ∀ z, 0 ≤ g z := by
    intro z
    exact Real.rpow_nonneg (vecEuclideanNorm_nonneg _) p
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have hPairIntegrable (t : ℝ) :
      Integrable (F t) μPair := by
    have hsegmentCont :
        Continuous
          (fun z : Vec d × Vec d =>
            segmentBlend z.1 t z.2) := by
      simpa only [segmentBlend_eq_smul_add] using!
        (((continuous_const_smul (1 - t)).comp
          continuous_snd).add
            ((continuous_const_smul t).comp continuous_fst))
    have hOnClosure :
        IntegrableOn (F t)
          (closure U ×ˢ closure U)
          (volume.prod volume) :=
      (hgCont.comp hsegmentCont).continuousOn
        |>.integrableOn_compact
          (hclosureCompact.prod hclosureCompact)
    have hOnProduct :
        IntegrableOn (F t) (U ×ˢ U)
          (volume.prod volume) :=
      hOnClosure.mono_set
        (Set.prod_mono subset_closure subset_closure)
    change
      Integrable (F t)
        ((volume.restrict U).prod
          (volume.restrict U))
    rw [Measure.prod_restrict]
    exact hOnProduct
  have hFCont :
      Continuous (Function.uncurry F) := by
    have hsegmentCont :
        Continuous
          (fun q : ℝ × (Vec d × Vec d) =>
            segmentBlend q.2.1 q.1 q.2.2) := by
      simpa only [segmentBlend_eq_smul_add] using!
        (((continuous_const.sub continuous_fst).smul
          (continuous_snd.comp continuous_snd)).add
            (continuous_fst.smul
              (continuous_fst.comp continuous_snd)))
    exact hgCont.comp hsegmentCont
  have hTriple :
      Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          μPair) := by
    have hOnClosure :
        IntegrableOn (Function.uncurry F)
          (Set.Icc (0 : ℝ) 1 ×ˢ
            (closure U ×ˢ closure U))
          (volume.prod (volume.prod volume)) :=
      hFCont.continuousOn.integrableOn_compact
        (isCompact_Icc.prod
          (hclosureCompact.prod hclosureCompact))
    have hOnProduct :
        IntegrableOn (Function.uncurry F)
          (Set.Ioc (0 : ℝ) 1 ×ˢ (U ×ˢ U))
          (volume.prod (volume.prod volume)) :=
      hOnClosure.mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self
          (Set.prod_mono subset_closure subset_closure))
    change
      Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          ((volume.restrict U).prod
            (volume.restrict U)))
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact hOnProduct
  have hPairOscillation :
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p) μPair := by
    change
      Integrable
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        ((volume.restrict U).prod
          (volume.restrict U))
    simpa only [← Measure.prod_restrict, IntegrableOn] using
      integrableOn_prod_abs_sub_rpow_of_contDiff
        hU.isSobolevRegularDomain
        (hu.of_le (by simp)) hpNonneg
  have hIntervalSection :
      Integrable
        (fun z =>
          ∫ t in (0 : ℝ)..1, F t z) μPair := by
    have hsection :=
      hTriple.integral_prod_right
    simpa only [
      intervalIntegral.integral_of_le zero_le_one]
      using! hsection
  have hDiameterPowNonneg : 0 ≤ D ^ p :=
    Real.rpow_nonneg hD p
  have hRight :
      Integrable
        (fun z =>
          D ^ p * (∫ t in (0 : ℝ)..1, F t z))
        μPair :=
    hIntervalSection.const_mul (D ^ p)
  have hPairBound :
      (∫ z, |u z.1 - u z.2| ^ p ∂μPair) ≤
        ∫ z,
          D ^ p * (∫ t in (0 : ℝ)..1, F t z)
            ∂μPair := by
    refine integral_mono_ae
      hPairOscillation hRight ?_
    have hmeas : MeasurableSet (U ×ˢ U) :=
      hU.measurableSet.prod hU.measurableSet
    change
      (fun z : Vec d × Vec d =>
        |u z.1 - u z.2| ^ p) ≤ᵐ[
          (volume.restrict U).prod
            (volume.restrict U)]
        (fun z =>
          D ^ p * (∫ t in (0 : ℝ)..1, F t z))
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem hmeas] with z hz
    exact
      abs_sub_rpow_le_diameter_rpow_mul_integral_euclideanGradient_rpow
        hp hUDiameter hu hz.1 hz.2
  have hIntervalPair :
      IntervalIntegrable
        (fun t => ∫ z, F t z ∂μPair)
        volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      zero_le_one]
    exact hTriple.integral_prod_left
  let C : ℝ :=
    (2 : ℝ) ^ d * (volume U).toReal *
      ∫ z in U, g z ∂volume
  have hConstInterval :
      IntervalIntegrable (fun _ : ℝ => C)
        volume 0 1 :=
    intervalIntegrable_const
  have hIntervalBound :
      (∫ t in (0 : ℝ)..1,
        ∫ z, F t z ∂μPair) ≤ C := by
    calc
      (∫ t in (0 : ℝ)..1,
          ∫ z, F t z ∂μPair) ≤
          ∫ _t in (0 : ℝ)..1, C := by
        refine intervalIntegral.integral_mono_on
          zero_le_one hIntervalPair hConstInterval ?_
        intro t ht
        have hFubini :=
          integral_prod (F t) (hPairIntegrable t)
        have hSegment :=
          setIntegral_setIntegral_comp_segmentBlend_le_two_pow_mul
            hU hgCont hgNonneg t ht
        change (∫ z, F t z ∂μPair) ≤ C
        rw [hFubini]
        simpa only [F, g, μPair, μU, volumeOn, C] using
          hSegment
      _ = C := by
        simp
  calc
    (∫ x in U, ∫ y in U,
        |u x - u y| ^ p ∂volume ∂volume) =
        ∫ z, |u z.1 - u z.2| ^ p ∂μPair := by
      symm
      simpa only [μPair, μU, volumeOn] using
        integral_prod
          (fun z : Vec d × Vec d =>
            |u z.1 - u z.2| ^ p)
          hPairOscillation
    _ ≤ ∫ z,
        D ^ p * (∫ t in (0 : ℝ)..1, F t z)
          ∂μPair :=
      hPairBound
    _ = D ^ p *
        ∫ z, (∫ t in (0 : ℝ)..1, F t z) ∂μPair := by
      rw [integral_const_mul]
    _ = D ^ p *
        ∫ t in (0 : ℝ)..1,
          ∫ z, F t z ∂μPair := by
      have hTripleInterval :
          Integrable (Function.uncurry F)
            ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
              μPair) := by
        simpa only [Set.uIoc_of_le zero_le_one] using
          hTriple
      rw [intervalIntegral_integral_swap hTripleInterval]
    _ ≤ D ^ p * C :=
      mul_le_mul_of_nonneg_left hIntervalBound
        hDiameterPowNonneg
    _ = D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume) := by
      rfl

/-- Diameter-only smooth Poincaré inequality in integral-power form.

The constant `2 ^ d` is independent of the real exponent `p ≥ 1`. -/
theorem setIntegral_abs_sub_integralAverage_rpow_le_two_pow_mul
    {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    (∫ x in U,
        |u x - integralAverage U u| ^ p ∂volume) ≤
      (2 : ℝ) ^ d * D ^ p *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume := by
  have hvolReal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne'
  have hvolInvNonneg : 0 ≤ (volume U).toReal⁻¹ := by
    positivity
  have hJensen :=
    setIntegral_abs_sub_integralAverage_rpow_le
      hU hu hp hUPos hUTop
  have hPairwise :=
    setIntegral_setIntegral_abs_sub_rpow_le
      hU hUDiameter hD hu hp
  calc
    (∫ x in U,
        |u x - integralAverage U u| ^ p ∂volume) ≤
        (volume U).toReal⁻¹ *
          ∫ x in U, ∫ y in U,
            |u x - u y| ^ p ∂volume ∂volume :=
      hJensen
    _ ≤ (volume U).toReal⁻¹ *
        (D ^ p * ((2 : ℝ) ^ d * (volume U).toReal *
          ∫ z in U,
            vecEuclideanNorm (classicalGradient u z) ^ p
              ∂volume)) :=
      mul_le_mul_of_nonneg_left hPairwise
        hvolInvNonneg
    _ = (2 : ℝ) ^ d * D ^ p *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume := by
      field_simp [hvolReal]

/-- Mean-zero specialization of the smooth integral-power Poincaré
inequality. -/
theorem setIntegral_abs_rpow_le_two_pow_mul_of_meanZeroOn
    {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (huMean : MeanZeroOn U u) :
    (∫ x in U, |u x| ^ p ∂volume) ≤
      (2 : ℝ) ^ d * D ^ p *
        ∫ z in U,
          vecEuclideanNorm (classicalGradient u z) ^ p
            ∂volume := by
  have h :=
    setIntegral_abs_sub_integralAverage_rpow_le_two_pow_mul
      hU hUDiameter hD hu hp hUPos hUTop
  rw [integralAverage_eq_zero_of_meanZeroOn huMean] at h
  simpa only [sub_zero] using h

end PDE
