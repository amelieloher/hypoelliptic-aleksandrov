module

public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Strong convergence of parabolic mollification

This module proves the finite-exponent approximate-identity theorem for the
right convolution fixed by `WeakJetMollifier`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise Topology

private theorem parabolicConvolution_eq_leftConvolution {d : Nat}
    (f rho : TimeVelocity d → Real) :
    parabolicConvolution f rho =
      rho ⋆[ContinuousLinearMap.lsmul Real Real,
        (volume : Measure (TimeVelocity d))] f := by
  rw [← convolution_flip]
  ext z
  simp only [parabolicConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  change f y * rho (z - y) = rho (z - y) * f y
  exact mul_comm _ _

private theorem abs_integral_rpow_le_integral_abs_rpow
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → Real} {q : Real} (hq : 1 ≤ q)
    (hf : Integrable f μ)
    (hfp : Integrable (fun x => |f x| ^ q) μ) :
    |∫ x, f x ∂μ| ^ q ≤ ∫ x, |f x| ^ q ∂μ := by
  have hqNonneg : 0 ≤ q := zero_le_one.trans hq
  have hJensen :
      (∫ x, |f x| ∂μ) ^ q ≤ ∫ x, |f x| ^ q ∂μ := by
    simpa only [Function.comp_apply] using
      (convexOn_rpow hq).map_integral_le
        (Real.continuous_rpow_const hqNonneg).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun x => abs_nonneg (f x)) hf.abs hfp
  exact
    (Real.rpow_le_rpow (abs_nonneg _)
      MeasureTheory.abs_integral_le_integral_abs hqNonneg).trans hJensen

private theorem isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {rho : α → Real}
    (hrhoNonneg : ∀ x, 0 ≤ rho x)
    (hrhoInt : Integrable rho μ)
    (hrhoOne : ∫ x, rho x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (rho x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hrhoInt
    (ae_of_all _ hrhoNonneg), hrhoOne]
  simp

private theorem lintegral_comp_sub_right {d : Nat}
    (f : TimeVelocity d → ENNReal) (hf : Measurable f)
    (t : TimeVelocity d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (TimeVelocity d)) =
      ∫⁻ x, f x ∂(volume : Measure (TimeVelocity d)) := by
  have heq :
      (fun x => f (x - t)) = f ∘ ((· + (-t)) : TimeVelocity d → TimeVelocity d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap :
      Measure.map (fun x : TimeVelocity d => x + (-t))
          (volume : Measure (TimeVelocity d)) = volume := by
    simpa using
      (map_add_right_eq_self (μ := (volume : Measure (TimeVelocity d))) (-t))
  rw [hmap]

private theorem fubini_translation_key {d : Nat}
    (rho : TimeVelocity d → ENNReal) (g : TimeVelocity d → Real)
    (q : Real) (hrho : Measurable rho) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t,
        rho t * (ENNReal.ofReal |g (x - t)|) ^ q
          ∂(volume : Measure (TimeVelocity d)) ∂volume =
      (∫⁻ t, rho t ∂(volume : Measure (TimeVelocity d))) *
        (∫⁻ x, (ENNReal.ofReal |g x|) ^ q
          ∂(volume : Measure (TimeVelocity d))) := by
  have hswap :
      ∫⁻ x, ∫⁻ t,
          rho t * (ENNReal.ofReal |g (x - t)|) ^ q
            ∂(volume : Measure (TimeVelocity d)) ∂volume =
        ∫⁻ t, ∫⁻ x,
          rho t * (ENNReal.ofReal |g (x - t)|) ^ q
            ∂(volume : Measure (TimeVelocity d)) ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hrho.comp measurable_snd).aemeasurable
    · apply Measurable.aemeasurable
      apply Measurable.pow_const
      exact ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (hg.comp (measurable_fst.sub measurable_snd)))
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x,
          rho t * (ENNReal.ofReal |g (x - t)|) ^ q
            ∂(volume : Measure (TimeVelocity d)) ∂volume =
        ∫⁻ t, rho t * ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ q
          ∂(volume : Measure (TimeVelocity d)) ∂volume := by
    congr 1
    ext t
    exact lintegral_const_mul _ <|
      Measurable.pow_const
        (ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp (hg.comp (measurable_id.sub measurable_const)))) q
  rw [hfactor]
  have htrans : ∀ t,
      ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ q
          ∂(volume : Measure (TimeVelocity d)) =
        ∫⁻ x, (ENNReal.ofReal |g x|) ^ q
          ∂(volume : Measure (TimeVelocity d)) := by
    intro t
    exact lintegral_comp_sub_right _
      (Measurable.pow_const
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)) q) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hrho, mul_comm]

private theorem integral_withDensity_ofReal_eq_integral_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → Real}
    (hfNonneg : ∀ x, 0 ≤ f x) (hfMeas : AEMeasurable f μ) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x ∂μ := by
  have heq : (fun x => ENNReal.ofReal (f x)) =
      fun x => (Real.toNNReal (f x) : ENNReal) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hfNonneg x), Real.toNNReal_of_nonneg (hfNonneg x)]
  rw [heq, integral_withDensity_eq_integral_smul₀ hfMeas.real_toNNReal]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hfNonneg x)]

private theorem young_left_convolution_nonneg_integral_one
    {d : Nat} {rho g : TimeVelocity d → Real} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hrhoNonneg : ∀ x, 0 ≤ rho x)
    (hrhoInt : Integrable rho volume)
    (hrhoOne : ∫ x, rho x = 1)
    (hrhoMeas : Measurable rho)
    (hgMeas : Measurable g) :
    eLpNorm (rho ⋆[ContinuousLinearMap.lsmul Real Real, volume] g) p volume ≤
      eLpNorm g p volume := by
  have hpNeZero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hpNeZero hpTop
  have hpReal : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpTop).mpr hp
  let mu : Measure (TimeVelocity d) :=
    volume.withDensity fun t => ENNReal.ofReal (rho t)
  letI : IsProbabilityMeasure mu :=
    isProbabilityMeasure_withDensity_ofReal hrhoNonneg hrhoInt hrhoOne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    (AEStronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hrhoMeas.aestronglyMeasurable hgMeas.aestronglyMeasurable)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop hgMeas.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini := fubini_translation_key (d := d)
    (fun t => ENNReal.ofReal (rho t)) g p.toReal
    hrhoMeas.ennreal_ofReal hgMeas
  have hrhoLintegralOne :
      ∫⁻ t, ENNReal.ofReal (rho t) ∂(volume : Measure (TimeVelocity d)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hrhoInt
      (ae_of_all _ hrhoNonneg), hrhoOne]
    simp
  have hpointwise : ∀ x,
      ‖(rho ⋆[ContinuousLinearMap.lsmul Real Real, volume] g) x‖ₑ ^ p.toReal ≤
        ∫⁻ t, ENNReal.ofReal (rho t) *
          (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heqIntegral :
        ∫ t, rho t * g (x - t) = ∫ t, g (x - t) ∂mu := by
      symm
      exact integral_withDensity_ofReal_eq_integral_mul hrhoNonneg hrhoMeas.aemeasurable
    rw [heqIntegral]
    by_cases hgInt : Integrable (fun t => g (x - t)) mu
    · by_cases hgPowInt : Integrable (fun t => |g (x - t)| ^ p.toReal) mu
      · have hJensen := abs_integral_rpow_le_integral_abs_rpow hpReal hgInt hgPowInt
        have heqPow :
            ∫ t, |g (x - t)| ^ p.toReal ∂mu =
              (∫⁻ t, ENNReal.ofReal (rho t) *
                (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul
            hrhoNonneg hrhoMeas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hrhoNonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpPos.le]
          · exact ae_of_all _ fun t =>
              mul_nonneg (hrhoNonneg t) (Real.rpow_nonneg (abs_nonneg _) _)
          · have hAbsPowMeas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
              have hcont : Continuous (fun y : Real => |y| ^ p.toReal) :=
                continuous_abs.rpow_const (fun _ => Or.inr hpPos.le)
              exact hcont.measurable.comp
                (hgMeas.comp (measurable_const.sub measurable_id))
            exact (hrhoMeas.mul hAbsPowMeas).aestronglyMeasurable
        calc
          ENNReal.ofReal |∫ t, g (x - t) ∂mu| ^ p.toReal =
              ENNReal.ofReal (|∫ t, g (x - t) ∂mu| ^ p.toReal) := by
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpPos.le]
          _ ≤ ENNReal.ofReal (∫ t, |g (x - t)| ^ p.toReal ∂mu) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ = ENNReal.ofReal
              ((∫⁻ t, ENNReal.ofReal (rho t) *
                (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal) := by
            rw [heqPow]
          _ ≤ ∫⁻ t, ENNReal.ofReal (rho t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnotFinite :
            ∫⁻ t, ENNReal.ofReal (rho t) *
                (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume = ∞ := by
          have heq :
              ∫⁻ t, ENNReal.ofReal (rho t) *
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume =
                ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂mu := by
            have hsub : Measurable (fun t : TimeVelocity d => x - t) :=
              measurable_const.sub measurable_id
            have hAbsMeas : Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp (hgMeas.comp hsub)
            have hMeasPow : Measurable
                (fun t => (ENNReal.ofReal |g (x - t)|) ^ p.toReal) :=
              Measurable.pow_const hAbsMeas.ennreal_ofReal p.toReal
            symm
            convert lintegral_withDensity_eq_lintegral_mul
              volume hrhoMeas.ennreal_ofReal hMeasPow using 2
          rw [heq]
          have hAbsPowNonneg : ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t => Real.rpow_nonneg (abs_nonneg _) _
          have hAbsPowMeas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont : Continuous (fun y : Real => |y| ^ p.toReal) :=
              continuous_abs.rpow_const (fun _ => Or.inr hpPos.le)
            have hsub : Measurable (fun t : TimeVelocity d => x - t) :=
              measurable_const.sub measurable_id
            exact hcont.measurable.comp (hgMeas.comp hsub)
          have htop :
              ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂mu = ∞ := by
            rw [← lintegral_ofReal_ne_top_iff_integrable
              hAbsPowMeas.aestronglyMeasurable (ae_of_all _ hAbsPowNonneg)] at hgPowInt
            push_neg at hgPowInt
            convert hgPowInt using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpPos.le]
          rw [htop]
        simp [hnotFinite]
    · rw [integral_undef hgInt]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hpPos]
      exact zero_le
  calc
    ∫⁻ x, ‖(rho ⋆[ContinuousLinearMap.lsmul Real Real, volume] g) x‖ₑ ^ p.toReal ∂volume ≤
        ∫⁻ x, ∫⁻ t, ENNReal.ofReal (rho t) *
          (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ = (∫⁻ t, ENNReal.ofReal (rho t) ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := hfubini
    _ = 1 * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := by rw [hrhoLintegralOne]
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume := one_mul _
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

/-- Normalized nonnegative right convolution is contractive in every finite
`Lᵖ` exponent on time--velocity product volume. -/
theorem eLpNorm_parabolicConvolution_le_of_nonneg_integral_one
    {d : Nat} {rho g : TimeVelocity d → Real} {p : ENNReal}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hrhoNonneg : ∀ x, 0 ≤ rho x)
    (hrhoInt : Integrable rho volume)
    (hrhoOne : ∫ x, rho x = 1)
    (hrhoMeas : Measurable rho)
    (hgMeas : AEMeasurable g volume) :
    eLpNorm (parabolicConvolution g rho) p volume ≤ eLpNorm g p volume := by
  let g' : TimeVelocity d → Real := hgMeas.mk g
  have hconv : parabolicConvolution g rho = parabolicConvolution g' rho := by
    rw [parabolicConvolution_eq_leftConvolution, parabolicConvolution_eq_leftConvolution]
    simpa [g'] using
      (convolution_congr (L := ContinuousLinearMap.lsmul Real Real)
        (μ := (volume : Measure (TimeVelocity d)))
        (h1 := Filter.EventuallyEq.rfl) (h2 := hgMeas.ae_eq_mk))
  rw [hconv, parabolicConvolution_eq_leftConvolution]
  calc
    eLpNorm (rho ⋆[ContinuousLinearMap.lsmul Real Real, volume] g') p volume ≤
        eLpNorm g' p volume :=
      young_left_convolution_nonneg_integral_one hpOne hpTop hrhoNonneg hrhoInt hrhoOne
        hrhoMeas hgMeas.measurable_mk
    _ = eLpNorm g p volume := eLpNorm_congr_ae hgMeas.ae_eq_mk.symm

/-- Every fixed normalized parabolic mollification of an `Lᵖ` function is in
the same finite-exponent `Lᵖ` space. -/
theorem memLp_parabolicConvolution_parabolicMollifier
    {d : Nat} {p : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (TimeVelocity d))) (n : Nat) :
    MemLp (parabolicConvolution f (parabolicMollifier d n)) p
      (volume : Measure (TimeVelocity d)) := by
  exact (eLpNorm_parabolicConvolution_le_of_nonneg_integral_one hpOne hpTop
      (parabolicMollifier_nonneg d n)
      ((contDiff_parabolicMollifier d n).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_parabolicMollifier d n))
      (integral_parabolicMollifier d n)
      (contDiff_parabolicMollifier d n).continuous.measurable
      hf.aemeasurable).trans_lt hf.eLpNorm_lt_top

private theorem tendsto_eLpNorm_parabolicConvolution_sub_of_contDiff_hasCompactSupport
    {d : Nat} {p : ENNReal} {g : TimeVelocity d → Real}
    (hpTop : p ≠ ∞) (hgCompact : HasCompactSupport g)
    (hg : ContDiff Real (⊤ : ℕ∞) g) :
    Tendsto (fun n : Nat =>
      eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z)
        p volume) atTop (nhds 0) := by
  let s : Set (TimeVelocity d) :=
    tsupport g + Metric.closedBall (0 : TimeVelocity d) (1 : Real)
  have hsCompact : IsCompact s :=
    hgCompact.isCompact.add (isCompact_closedBall (0 : TimeVelocity d) (1 : Real))
  have hsMeas : MeasurableSet s := hsCompact.measurableSet
  have hsFinite : (volume : Measure (TimeVelocity d)) s ≠ ∞ :=
    hsCompact.measure_lt_top.ne
  have hpowTop : (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsFinite).ne
  let c : Real := ((volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal)).toReal
  have hcNonneg : 0 ≤ c := ENNReal.toReal_nonneg
  have hpow : ENNReal.ofReal c = (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := by
    dsimp only [c]
    exact ENNReal.ofReal_toReal hpowTop
  have hgUniform : UniformContinuous g :=
    hg.continuous.uniformContinuous_of_tendsto_cocompact hgCompact.is_zero_at_infty
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  by_cases hetaTop : eta = ∞
  · exact Eventually.of_forall fun n => by simp [hetaTop]
  let delta : Real := eta.toReal / (c + 1)
  have hetaReal : 0 < eta.toReal := ENNReal.toReal_pos heta.ne' hetaTop
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨eps, hepsPos, heps⟩ := (Metric.uniformContinuous_iff.1 hgUniform) delta hdelta
  have hscale : ∀ᶠ n : Nat in atTop, parabolicMollifierScale n < eps :=
    (tendsto_order.1 tendsto_parabolicMollifierScale_zero).2 eps hepsPos
  filter_upwards [hscale] with n hn
  have hball : ∀ z x, x ∈ Metric.ball z (parabolicMollifierBump d n).rOut →
      dist (g x) (g z) ≤ delta := by
    intro z x hx
    apply (heps (a := x) (b := z) ?_).le
    simpa only [dist_comm, parabolicMollifierBump_rOut] using lt_trans hx hn
  have hpoint : ∀ z,
      dist (parabolicConvolution g (parabolicMollifier d n) z) (g z) ≤ delta := by
    intro z
    rw [parabolicConvolution_eq_leftConvolution]
    exact ContDiffBump.dist_normed_convolution_le
      (φ := parabolicMollifierBump d n) hg.continuous.aestronglyMeasurable (hball z)
  have hsupportKernel : Function.support (parabolicMollifier d n) ⊆
      Metric.closedBall (0 : TimeVelocity d) (1 : Real) := by
    rw [support_parabolicMollifier]
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by simpa using parabolicMollifierScale_le_one n)))
  have hsupportConv : Function.support
      (parabolicConvolution g (parabolicMollifier d n)) ⊆ s := by
    rw [show parabolicConvolution g (parabolicMollifier d n) =
        g ⋆[ContinuousLinearMap.mul Real Real, volume] (parabolicMollifier d n) by rfl]
    exact (support_convolution_subset (ContinuousLinearMap.mul Real Real)).trans
      (add_subset_add (subset_tsupport g) hsupportKernel)
  have hsupportG : Function.support g ⊆ s := by
    intro z hz
    exact ⟨z, subset_tsupport g hz, 0,
      Metric.mem_closedBall_self (by norm_num), by simp⟩
  have hnorm :
      eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤
        ENNReal.ofReal delta * (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := by
    exact eLpNorm_sub_le_of_dist_bdd volume hpTop hsMeas.nullMeasurableSet hdelta.le
      (((contDiff_parabolicConvolution
        (hg.continuous.locallyIntegrable)
        (contDiff_parabolicMollifier d n)
        (hasCompactSupport_parabolicMollifier d n)).continuous.sub
        hg.continuous).aestronglyMeasurable) hpoint hsupportConv hsupportG
  have hdeltaMul : delta * c ≤ eta.toReal := by
    have hfrac : c / (c + 1) ≤ 1 := by
      have hc : c ≤ c + 1 := by linarith
      have hdenom : 0 ≤ c + 1 := by linarith
      simpa only using div_le_one_of_le₀ hc hdenom
    calc
      delta * c = eta.toReal * (c / (c + 1)) := by
        dsimp [delta]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ eta.toReal * 1 := mul_le_mul_of_nonneg_left hfrac hetaReal.le
      _ = eta.toReal := by ring
  calc
    eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤
        ENNReal.ofReal delta * (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := hnorm
    _ = ENNReal.ofReal (delta * c) := by
      rw [← hpow, ← ENNReal.ofReal_mul]
      exact hdelta.le
    _ ≤ eta := by
      rw [← ENNReal.ofReal_toReal hetaTop]
      exact ENNReal.ofReal_le_ofReal hdeltaMul

private theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_le
    {d : Nat} {p eps : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) (hf : MemLp f p volume)
    (heps : eps ≠ 0) :
    ∃ g : TimeVelocity d → Real, HasCompactSupport g ∧ ContDiff Real (⊤ : ℕ∞) g ∧
      eLpNorm (f - g) p volume ≤ eps := by
  by_cases hepsTop : eps = ∞
  · refine ⟨0, HasCompactSupport.zero, contDiff_const, ?_⟩
    rw [hepsTop]
    exact le_top
  let r : Real := eps.toReal / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (ENNReal.toReal_pos heps hepsTop) (by norm_num)
  obtain ⟨g, hgCompact, hgSmooth, hg⟩ := hf.exist_eLpNorm_sub_le hpTop hpOne hr
  refine ⟨g, hgCompact, hgSmooth, hg.trans ?_⟩
  rw [show eps = ENNReal.ofReal eps.toReal by
    exact (ENNReal.ofReal_toReal hepsTop).symm]
  apply ENNReal.ofReal_le_ofReal
  dsimp [r]
  exact half_le_self ENNReal.toReal_nonneg

/-- Strong finite-exponent convergence for the right parabolic
convolution against the actual normalized shrinking mollifier sequence. -/
theorem tendsto_eLpNorm_parabolicConvolution_sub
    {d : Nat} {p : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (TimeVelocity d))) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution f (parabolicMollifier d n) z - f z)
      p (volume : Measure (TimeVelocity d))) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  by_cases hetaTop : eta = ∞
  · exact Eventually.of_forall fun n => by simp [hetaTop]
  obtain ⟨eta1, heta1Pos, heta1⟩ :=
    exists_Lp_half (μ := (volume : Measure (TimeVelocity d))) (ε := Real) (p := p) heta.ne'
  obtain ⟨eta2, heta2Pos, heta2⟩ :=
    exists_Lp_half (μ := (volume : Measure (TimeVelocity d))) (ε := Real) (p := p) heta1Pos.ne'
  let eps : ENNReal := min eta1 eta2
  have hepsPos : 0 < eps := lt_min heta1Pos heta2Pos
  obtain ⟨g, hgCompact, hgSmooth, hfg⟩ :=
    exists_contDiff_hasCompactSupport_eLpNorm_sub_le hpOne hpTop hf hepsPos.ne'
  have hgMem : MemLp g p volume :=
    hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact
  have hdiffMem : MemLp (f - g) p volume := hf.sub hgMem
  have hkernelCont (n : Nat) : Continuous (parabolicMollifier d n) :=
    (contDiff_parabolicMollifier d n).continuous
  have hdiffLoc : LocallyIntegrable (f - g) volume := hdiffMem.locallyIntegrable hpOne
  have hgLoc : LocallyIntegrable g volume := hgMem.locallyIntegrable hpOne
  have hlin (n : Nat) :
      parabolicConvolution ((f - g) + g) (parabolicMollifier d n) =
        parabolicConvolution (f - g) (parabolicMollifier d n) +
          parabolicConvolution g (parabolicMollifier d n) := by
    apply ConvolutionExists.add_distrib
    · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
        (ContinuousLinearMap.mul Real Real) hdiffLoc (hkernelCont n)
    · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
        (ContinuousLinearMap.mul Real Real) hgLoc (hkernelCont n)
  have hident (n : Nat) :
      (fun z => parabolicConvolution f (parabolicMollifier d n) z -
        parabolicConvolution g (parabolicMollifier d n) z) =
        parabolicConvolution (f - g) (parabolicMollifier d n) := by
    funext z
    have hz := congrFun (hlin n) z
    dsimp only [Pi.add_apply] at hz
    have hsum : (f - g) + g = f := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    rw [hsum] at hz
    linarith
  have hmiddleTendsto :=
    tendsto_eLpNorm_parabolicConvolution_sub_of_contDiff_hasCompactSupport
      (d := d) (p := p) hpTop hgCompact hgSmooth
  have hfirstEventually : ∀ᶠ n : Nat in atTop, eLpNorm
      (fun z => parabolicConvolution f (parabolicMollifier d n) z -
        parabolicConvolution g (parabolicMollifier d n) z) p volume ≤ eta1 :=
    Filter.Eventually.of_forall fun n => by
      rw [hident n]
      exact (eLpNorm_parabolicConvolution_le_of_nonneg_integral_one hpOne hpTop
        (parabolicMollifier_nonneg d n)
        ((contDiff_parabolicMollifier d n).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_parabolicMollifier d n))
        (integral_parabolicMollifier d n)
        ((contDiff_parabolicMollifier d n).continuous.measurable)
        hdiffMem.aestronglyMeasurable.aemeasurable).trans
          (hfg.trans (min_le_left _ _))
  have hmiddleEventually : ∀ᶠ n : Nat in atTop, eLpNorm
      (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤ eta2 :=
    ENNReal.tendsto_nhds_zero.1 hmiddleTendsto eta2 heta2Pos
  filter_upwards [hfirstEventually, hmiddleEventually] with n hfirst hmiddle
  let a : TimeVelocity d → Real := fun z =>
    parabolicConvolution f (parabolicMollifier d n) z -
      parabolicConvolution g (parabolicMollifier d n) z
  let b : TimeVelocity d → Real := fun z =>
    (parabolicConvolution g (parabolicMollifier d n) z - g z) + (g z - f z)
  have haMeas : AEStronglyMeasurable a volume := by
    dsimp [a]
    exact ((contDiff_parabolicConvolution (hf.locallyIntegrable hpOne)
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)).continuous.sub
      (contDiff_parabolicConvolution (hgMem.locallyIntegrable hpOne)
        (contDiff_parabolicMollifier d n)
        (hasCompactSupport_parabolicMollifier d n)).continuous).aestronglyMeasurable
  have hbMeas : AEStronglyMeasurable b volume := by
    dsimp [b]
    exact ((contDiff_parabolicConvolution (hgMem.locallyIntegrable hpOne)
      (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)).continuous.sub
      hgSmooth.continuous).aestronglyMeasurable.add (hgMem.sub hf).aestronglyMeasurable
  have hthird : eLpNorm (fun z => g z - f z) p volume ≤ eta2 := by
    change eLpNorm (g - f) p volume ≤ eta2
    rw [eLpNorm_sub_comm]
    exact hfg.trans (min_le_right _ _)
  have hcombo : eLpNorm b p volume < eta1 := by
    exact heta2 _ _ hmiddle hthird
  have hsum : eLpNorm (a + b) p volume < eta := heta1 _ _ hfirst hcombo.le

  have hdecomp :
      (fun z => parabolicConvolution f (parabolicMollifier d n) z - f z) = a + b := by
    funext z
    dsimp [a, b, Pi.add_apply]
    ring
  rw [hdecomp]
  exact hsum.le

namespace ParabolicW12Function

/-- The stored value representative converges strongly under parabolic
mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_toFun_sub
    {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d n) z - w.toFun z)
      p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.memLp
      change MemLp w.toFun p ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- The stored time-derivative representative converges strongly under
parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_timeDeriv_sub
    {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution w.timeDeriv (parabolicMollifier d n) z - w.timeDeriv z)
      p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.timeDeriv_memLp
      change MemLp w.timeDeriv p ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- Each stored velocity-gradient representative converges strongly under
parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_velocityGrad_sub
    {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) (i : Fin d) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution (fun y => w.velocityGrad y i)
        (parabolicMollifier d n) z - w.velocityGrad z i) p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.velocityGrad_memLp i
      change MemLp (fun z => w.velocityGrad z i) p
        ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- Each stored ordered velocity-Hessian representative converges strongly
under parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_velocityHessian_sub
    {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) (i j : Fin d) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution (fun y => w.velocityHessian y i j)
        (parabolicMollifier d n) z - w.velocityHessian z i j) p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.velocityHessian_memLp i j
      change MemLp (fun z => w.velocityHessian z i j) p
        ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
