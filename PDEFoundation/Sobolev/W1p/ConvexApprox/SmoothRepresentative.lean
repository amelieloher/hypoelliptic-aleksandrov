module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth representatives for convex-domain approximation

This file defines the globally smooth representative of convex approximation.
It also records the measurable change of variables, exact `L^p` bounds, and
integrability lemmas needed by the later density and weak-derivative modules.

The convolution contraction used below is kept private: it is an implementation
lemma for this layer, not a second public Sobolev-space API.
-/

@[expose] public section

open scoped ENNReal Pointwise Convolution

namespace PDE

open MeasureTheory

noncomputable section

private theorem isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ}
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ μ)
    (hρOne : ∫ x, ρ x ∂μ = 1) :
    IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρInt
    (ae_of_all _ hρNonneg), hρOne]
  simp

private theorem lintegral_comp_sub_right
    {d : ℕ} (f : Vec d → ℝ≥0∞) (hf : Measurable f)
    (t : Vec d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) =
      ∫⁻ x, f x ∂(volume : Measure (Vec d)) := by
  have heq :
      (fun x => f (x - t)) =
        f ∘ ((· + (-t)) : Vec d → Vec d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap :
      Measure.map (fun x : Vec d => x + (-t))
          (volume : Measure (Vec d)) =
        volume := by
    simpa using
      (map_add_right_eq_self
        (μ := (volume : Measure (Vec d))) (-t))
  rw [hmap]

private theorem fubini_translation_key
    {d : ℕ} (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ)
    (p : ℝ) (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t,
        ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
          ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) *
        (∫⁻ x, (ENNReal.ofReal |g x|) ^ p
          ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · apply Measurable.aemeasurable
      apply Measurable.pow_const
      exact
        ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp
            (hg.comp (measurable_fst.sub measurable_snd)))
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume =
        ∫⁻ t, ρ t *
          ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume := by
    congr 1
    ext t
    exact
      lintegral_const_mul _ <|
        Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp
              (hg.comp
                (measurable_id.sub measurable_const)))) p
  rw [hfactor]
  have htrans :
      ∀ t,
        ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
            ∂(volume : Measure (Vec d)) =
          ∫⁻ x, (ENNReal.ofReal |g x|) ^ p
            ∂volume := by
    intro t
    exact
      lintegral_comp_sub_right _
        (Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private theorem integral_withDensity_ofReal_eq_integral_mul
    {d : ℕ} {f g : Vec d → ℝ}
    (hfNonneg : ∀ x, 0 ≤ f x)
    (hfMeas : AEMeasurable f volume) :
    ∫ x, g x
        ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq :
      (fun x => ENNReal.ofReal (f x)) =
        fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hfNonneg x),
      Real.toNNReal_of_nonneg (hfNonneg x)]
  rw [heq]
  rw [integral_withDensity_eq_integral_smul₀
    (hfMeas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (hfNonneg x)]

private theorem young_convolution_nonneg_integral_one
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ volume)
    (hρOne : ∫ x, ρ x = 1)
    (hρMeas : Measurable ρ)
    (hgMeas : Measurable g) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume := by
  have hpNeZero : p ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpPos : 0 < p.toReal :=
    ENNReal.toReal_pos hpNeZero hpTop
  have hpOne : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact
      (ENNReal.toReal_le_toReal
        ENNReal.one_ne_top hpTop).mpr hp
  let μ : Measure (Vec d) :=
    volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure μ :=
    isProbabilityMeasure_withDensity_ofReal
      hρNonneg hρInt hρOne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    (hρMeas.aestronglyMeasurable.convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hgMeas.aestronglyMeasurable)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    hgMeas.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _
    (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini :=
    fubini_translation_key (d := d)
      (fun t => ENNReal.ofReal (ρ t)) g p.toReal
      hρMeas.ennreal_ofReal hgMeas
  have hρLintegralOne :
      ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρInt
      (ae_of_all _ hρNonneg), hρOne]
    simp
  have hpointwise :
      ∀ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
            p.toReal ≤
          ∫⁻ t,
            ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal
            ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heqIntegral :
        ∫ t, ρ t * g (x - t) =
          ∫ t, g (x - t) ∂μ := by
      symm
      exact
        integral_withDensity_ofReal_eq_integral_mul
          hρNonneg hρMeas.aemeasurable
    rw [heqIntegral]
    by_cases hgInt :
        Integrable (fun t => g (x - t)) μ
    · by_cases hgPowInt :
          Integrable
            (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen :=
          abs_integral_rpow_le_integral_abs_rpow
            (μ := μ) hpOne hgInt hgPowInt
        have heqPow :
            ∫ t, |g (x - t)| ^ p.toReal ∂μ =
              (∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal
                  ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul
            hρNonneg hρMeas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρNonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          · exact
              ae_of_all _ fun t =>
                mul_nonneg (hρNonneg t)
                  (Real.rpow_nonneg (abs_nonneg _) _)
          · have hAbsPowMeas :
                Measurable
                  (fun t =>
                    |g (x - t)| ^ p.toReal) := by
              have hcont :
                  Continuous
                    (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const
                  (fun _ => Or.inr hpPos.le)
              exact
                hcont.measurable.comp
                  (hgMeas.comp
                    (measurable_const.sub measurable_id))
            exact
              (hρMeas.mul hAbsPowMeas).aestronglyMeasurable
        calc
          ENNReal.ofReal
                |∫ t, g (x - t) ∂μ| ^ p.toReal =
              ENNReal.ofReal
                (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          _ ≤
              ENNReal.ofReal
                (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ =
              ENNReal.ofReal
                ((∫⁻ t,
                    ENNReal.ofReal (ρ t) *
                      (ENNReal.ofReal |g (x - t)|) ^
                        p.toReal
                    ∂volume).toReal) := by
            rw [heqPow]
          _ ≤
              ∫⁻ t,
                ENNReal.ofReal (ρ t) *
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnotFinite :
            ∫⁻ t,
                ENNReal.ofReal (ρ t) *
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                ∂volume =
              ⊤ := by
          have heq :
              ∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal
                  ∂volume =
                ∫⁻ t,
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂μ := by
            have hsub :
                Measurable (fun t : Vec d => x - t) :=
              measurable_const.sub measurable_id
            have hAbsMeas :
                Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp
                (hgMeas.comp hsub)
            have hMeasPow :
                Measurable
                  (fun t =>
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal) :=
              Measurable.pow_const
                hAbsMeas.ennreal_ofReal p.toReal
            symm
            convert
              lintegral_withDensity_eq_lintegral_mul
                volume hρMeas.ennreal_ofReal hMeasPow
              using 2
          rw [heq]
          have hAbsPowNonneg :
              ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t =>
              Real.rpow_nonneg (abs_nonneg _) _
          have hAbsPowMeas :
              Measurable
                (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont :
                Continuous
                  (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const
                (fun _ => Or.inr hpPos.le)
            have hsub :
                Measurable (fun t : Vec d => x - t) :=
              measurable_const.sub measurable_id
            exact
              hcont.measurable.comp (hgMeas.comp hsub)
          have htop :
              ∫⁻ t,
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂μ =
                ⊤ := by
            rw [←
              lintegral_ofReal_ne_top_iff_integrable
                hAbsPowMeas.aestronglyMeasurable
                (ae_of_all _ hAbsPowNonneg)] at hgPowInt
            push Not at hgPowInt
            convert hgPowInt using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          rw [htop]
        simp [hnotFinite]
    · rw [integral_undef hgInt]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hpPos]
      exact zero_le
  calc
    ∫⁻ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
          p.toReal
        ∂volume ≤
      ∫⁻ x, ∫⁻ t,
          ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal
          ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ =
        (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal
            ∂volume) :=
      hfubini
    _ =
        1 *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal
            ∂volume) := by
      rw [hρLintegralOne]
    _ =
        ∫⁻ x,
          (ENNReal.ofReal |g x|) ^ p.toReal
          ∂volume := one_mul _
    _ =
        ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

private theorem young_convolution_nonneg_integral_one_of_aemeasurable
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ volume)
    (hρOne : ∫ x, ρ x = 1)
    (hρMeas : Measurable ρ)
    (hgMeas : AEMeasurable g volume) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume := by
  let g' : Vec d → ℝ :=
    hgMeas.mk g
  have hconv :
      convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution ρ g'
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    simpa [g'] using
      (convolution_congr
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure (Vec d)))
        (h1 := Filter.EventuallyEq.rfl)
        (h2 := hgMeas.ae_eq_mk))
  rw [hconv]
  calc
    eLpNorm
          (convolution ρ g'
            (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          p volume ≤
        eLpNorm g' p volume :=
      young_convolution_nonneg_integral_one
        hp hpTop hρNonneg hρInt hρOne hρMeas
        hgMeas.measurable_mk
    _ = eLpNorm g p volume :=
      eLpNorm_congr_ae hgMeas.ae_eq_mk.symm

/-- A globally smooth representative of convex-domain approximation. -/
noncomputable def convexApproxSmoothRepresentative
    {d : ℕ} (U : Set (Vec d)) (ρ u : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0)

theorem contDiff_convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : MeasurableSet U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convexApproxSmoothRepresentative
        U ρ u x0 r ε) := by
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hU]
    exact hu
  have huLocallyIntegrable :
      LocallyIntegrable (Set.indicator U u) volume :=
    huIndicator.locallyIntegrable hp
  have hconv :
      ContDiff ℝ (⊤ : ℕ∞)
        (scaledConvexApproxKernel ρ (ε * r) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator U u) :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume)
      (f := scaledConvexApproxKernel ρ (ε * r))
      (g := Set.indicator U u)
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr)
      (contDiff_scaledConvexApproxKernel hρ (ε * r))
      huLocallyIntegrable
  have haffine :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec d =>
          (1 - ε) • x + ε • x0) := by
    exact
      ((contDiff_id :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x : Vec d => x)).const_smul (1 - ε)).add contDiff_const
  exact hconv.comp haffine

theorem
    convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    convexApproxSmoothRepresentative U ρ u x0 r ε x =
      convexApproxSmoothing ρ u x0 r ε x := by
  simpa only [convexApproxSmoothRepresentative] using
    (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
      hU hρ hx hball hr hε hεOne).symm

theorem measurableEmbedding_convexApproxSample
    {d : ℕ} (x0 z : Vec d) (r ε : ℝ)
    (hε : ε < 1) :
    MeasurableEmbedding
      (convexApproxSample x0 z r ε) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have haNe : a ≠ 0 :=
    haPos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a haNe).trans
      (Homeomorph.addRight b)
  have heq :
      (fun x : Vec d => e x) =
        convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  rw [← heq]
  exact e.toMeasurableEquiv.measurableEmbedding

theorem map_restrict_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (_hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
        volume.restrict
          (convexApproxSample x0 z r ε '' U) := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have haNe : a ≠ 0 :=
    haPos.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    (Homeomorph.smulOfNeZero a haNe).trans
      (Homeomorph.addRight b)
  have heq :
      (fun x : Vec d => e x) =
        convexApproxSample x0 z r ε := by
    funext x
    simp [e, a, b, convexApproxSample]
  have hrestrict :
      Measure.map (convexApproxSample x0 z r ε)
          (volume.restrict U) =
        (Measure.map (convexApproxSample x0 z r ε)
          volume).restrict
            (convexApproxSample x0 z r ε '' U) := by
    have htmp :
        (volume.restrict U).map e =
          (volume.map e).restrict (e '' U) := by
      have h :=
        ((e.toMeasurableEquiv.restrict_map
          (μ := volume) (s := e '' U)).symm)
      simpa [Set.preimage_image_eq _ e.injective] using h
    simpa [heq] using htmp
  have hmapVolume :
      Measure.map (convexApproxSample x0 z r ε) volume =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume := by
    have hmapSmul :
        Measure.map (fun x : Vec d => a • x) volume =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
      have hpowNonneg : 0 ≤ a ^ d := by
        positivity
      let f : Vec d →ₗ[ℝ] Vec d :=
        a • (1 : Vec d →ₗ[ℝ] Vec d)
      have hf : LinearMap.det f ≠ 0 := by
        simp [f, haNe]
      have hdet : LinearMap.det f = a ^ d := by
        simp [f]
      have hmapf :=
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (ι := Fin d) (f := f) hf
      have hpowInvNonneg : 0 ≤ (a ^ d)⁻¹ := by
        positivity
      rw [hdet] at hmapf
      have hfun : (fun x : Vec d => a • x) = ⇑f := by
        funext x
        simp [f]
      rw [hfun]
      simpa only [abs_of_nonneg hpowInvNonneg] using
        hmapf
    calc
      Measure.map (convexApproxSample x0 z r ε) volume =
          (Measure.map (fun x : Vec d => a • x)
            volume).map
              (fun y : Vec d => y + b) := by
        rw [Measure.map_map
            (μ := volume)
            (g := fun y : Vec d => y + b)
            (f := fun x : Vec d => a • x)
            (measurable_id.add measurable_const)
            (measurable_const_smul a)]
        rfl
      _ =
          Measure.map (fun y : Vec d => y + b)
            (ENNReal.ofReal ((a ^ d)⁻¹) • volume) := by
        rw [hmapSmul]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) •
            Measure.map (fun y : Vec d => y + b)
              volume := by
        rw [Measure.map_smul (f := fun y : Vec d => y + b) _
          (measurable_add_const b).aemeasurable]
      _ =
          ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
        rw [map_add_right_eq_self]
      _ =
          ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume := by
        simp only [a]
  calc
    Measure.map (convexApproxSample x0 z r ε)
        (volume.restrict U) =
      (Measure.map (convexApproxSample x0 z r ε)
        volume).restrict
          (convexApproxSample x0 z r ε '' U) :=
      hrestrict
    _ =
        (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume).restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [hmapVolume]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
          volume.restrict
            (convexApproxSample x0 z r ε '' U) := by
      rw [Measure.restrict_smul]

theorem eLpNorm_comp_convexApproxSample_le
    {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {p : ENNReal}
    (hp : p ≠ ⊤) (hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1)
    (hmap :
      convexApproxSample x0 z r ε '' U ⊆ U) :
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  by_cases huMeas : AEStronglyMeasurable u (volume.restrict U)
  swap
  · have hc : ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / p).toReal ≠ 0 :=
      (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos (sub_pos.2 hε) d)))
        ENNReal.ofReal_ne_top).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable huMeas, ENNReal.mul_top hc]
    exact le_top
  calc
    eLpNorm
        (fun x => u (convexApproxSample x0 z r ε x))
        p (volume.restrict U) =
      eLpNorm u p
        (Measure.map
          (convexApproxSample x0 z r ε)
          (volume.restrict U)) := by
      symm
      exact
        (measurableEmbedding_convexApproxSample
          x0 z r ε hε).eLpNorm_map_measure
    _ =
        eLpNorm u p
          (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) •
            volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [map_restrict_convexApproxSample
        hU x0 z r ε hε]
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p
            (volume.restrict
              (convexApproxSample x0 z r ε '' U)) := by
      rw [eLpNorm_smul_measure_of_ne_top hp _ _
        (huMeas.mono_measure (Measure.restrict_mono_set volume hmap))]
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal •
          eLpNorm u p (volume.restrict U) := by
      exact
        smul_le_smul_of_nonneg_left
          (eLpNorm_mono_measure u
            (Measure.restrict_mono_set volume hmap))
          (by positivity)
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [smul_eq_mul]

theorem eLpNorm_convexApproxSmoothing_le
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) := by
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  have hUMeas : MeasurableSet U :=
    hU.isOpen.measurableSet
  have hmapZeroMapsTo :
      Set.MapsTo
        (convexApproxSample x0 0 r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr.le (by simp) hε.le (le_of_lt hεOne)
  have hmapZero :
      convexApproxSample x0 0 r ε '' U ⊆ U := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmapZeroMapsTo hx
  have hrepresentative :
      (fun x =>
        convexApproxSmoothing ρ u x0 r ε x) =ᵐ[
          volume.restrict U]
        fun x =>
          g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [ae_restrict_mem hUMeas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u)
        hU hρ hx hball hr hε hεOne)
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hconv :
      eLpNorm g p volume ≤
        eLpNorm (Set.indicator U u) p volume := by
    dsimp only [g]
    exact
      young_convolution_nonneg_integral_one_of_aemeasurable
        (d := d) hpOne hpTop
        (scaledConvexApproxKernel_nonneg hρ hεr)
        (integrable_scaledConvexApproxKernel hρ hεr)
        (integral_scaledConvexApproxKernel hρ hεr)
        (measurable_scaledConvexApproxKernel
          hρ.continuous (ε * r))
        huIndicator.aestronglyMeasurable.aemeasurable
  calc
    eLpNorm (convexApproxSmoothing ρ u x0 r ε)
        p (volume.restrict U) =
      eLpNorm
        (fun x =>
          g (convexApproxSample x0 0 r ε x))
        p (volume.restrict U) :=
      eLpNorm_congr_ae hrepresentative
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p (volume.restrict U) :=
      eLpNorm_comp_convexApproxSample_le
        hpTop hUMeas x0 0 r ε hεOne hmapZero
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm g p volume :=
      mul_le_mul' le_rfl
        (eLpNorm_mono_measure g
          Measure.restrict_le_self)
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (Set.indicator U u) p volume :=
      mul_le_mul' le_rfl hconv
    _ =
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm u p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUMeas]

theorem aestronglyMeasurable_convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p) (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    AEStronglyMeasurable
      (convexApproxSmoothing ρ u x0 r ε)
      (volume.restrict U) := by
  let g : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  have hUMeas : MeasurableSet U :=
    hU.isOpen.measurableSet
  have hrepresentative :
      (fun x =>
        convexApproxSmoothing ρ u x0 r ε x) =ᵐ[
          volume.restrict U]
        fun x =>
          g (convexApproxSample x0 0 r ε x) := by
    filter_upwards [ae_restrict_mem hUMeas] with x hx
    simpa [g, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u)
        hU hρ hx hball hr hε hεOne)
  have hεr : 0 < ε * r := by
    positivity
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hgContinuous : Continuous g := by
    dsimp only [g]
    exact
      HasCompactSupport.continuous_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := volume)
        (f := scaledConvexApproxKernel ρ (ε * r))
        (g := Set.indicator U u)
        (hasCompactSupport_scaledConvexApproxKernel
          hρ.compactSupport hεr)
        (continuous_scaledConvexApproxKernel
          hρ.continuous (ε * r))
        (huIndicator.locallyIntegrable hp)
  exact
    (aestronglyMeasurable_congr
      hrepresentative.symm).1
      ((hgContinuous.comp
        (continuous_convexApproxSample
          x0 0 r ε)).aestronglyMeasurable)

theorem memLpOn_convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)}
    {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    MemLpOn U p
      (convexApproxSmoothing ρ u x0 r ε) := by
  have hnorm :
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm u p (volume.restrict U) < ⊤ := by
    refine ENNReal.mul_lt_top ?_ hu.eLpNorm_lt_top
    exact
      ENNReal.rpow_lt_top_of_nonneg
        (by positivity) ENNReal.ofReal_ne_top
  exact
    lt_of_le_of_lt
      (eLpNorm_convexApproxSmoothing_le
        hU hρ hpOne hpTop hu
        hball hr hε hεOne)
      hnorm

theorem convexApproxSmoothing_sub_ae_eq
    {d : ℕ} {U : Set (Vec d)}
    {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hp : 1 ≤ p)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
      convexApproxSmoothing ρ
        (fun y => u y - v y) x0 r ε x) =ᵐ[
          volume.restrict U]
      fun x =>
        convexApproxSmoothing ρ u x0 r ε x -
          convexApproxSmoothing ρ v x0 r ε x := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel ρ (ε * r)
  let gu : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U u
  let gv : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U v
  let gw : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator U (fun y => u y - v y)
  have hUMeas : MeasurableSet U :=
    hU.isOpen.measurableSet
  have hεr : 0 < ε * r := by
    positivity
  have hkContinuous : Continuous k := by
    dsimp only [k]
    exact
      continuous_scaledConvexApproxKernel
        hρ.continuous (ε * r)
  have hkCompact : HasCompactSupport k := by
    dsimp only [k]
    exact
      hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport hεr
  have huIndicator :
      MemLp (Set.indicator U u) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hu
  have hvIndicator :
      MemLp (Set.indicator U v) p volume := by
    rw [memLp_indicator_iff_restrict hUMeas]
    exact hv
  have huLocallyIntegrable :
      LocallyIntegrable (Set.indicator U u) volume :=
    huIndicator.locallyIntegrable hp
  have hvLocallyIntegrable :
      LocallyIntegrable (Set.indicator U v) volume :=
    hvIndicator.locallyIntegrable hp
  have hnegvLocallyIntegrable :
      LocallyIntegrable
        ((-1 : ℝ) • Set.indicator U v) volume := by
    simpa using hvLocallyIntegrable.smul (-1 : ℝ)
  have hconvU :
      ConvolutionExists k (Set.indicator U u)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous huLocallyIntegrable
  have hconvNegV :
      ConvolutionExists k
        ((-1 : ℝ) • Set.indicator U v)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hkCompact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hkContinuous hnegvLocallyIntegrable
  have hindicatorSub :
      Set.indicator U (fun y => u y - v y) =
        Set.indicator U u +
          (-1 : ℝ) • Set.indicator U v := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, sub_eq_add_neg]
    · simp [hx]
  have hconvSub :
      gw = fun x => gu x - gv x := by
    ext x
    dsimp only [gw, gu, gv]
    rw [hindicatorSub,
      hconvU.distrib_add hconvNegV, convolution_smul]
    simp [sub_eq_add_neg]
  filter_upwards [ae_restrict_mem hUMeas] with x hx
  have huRepresentative :
      convexApproxSmoothing ρ u x0 r ε x =
        gu (convexApproxSample x0 0 r ε x) := by
    simpa [gu, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := u) hU hρ hx hball hr hε hεOne)
  have hvRepresentative :
      convexApproxSmoothing ρ v x0 r ε x =
        gv (convexApproxSample x0 0 r ε x) := by
    simpa [gv, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := v) hU hρ hx hball hr hε hεOne)
  have hwRepresentative :
      convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε x =
        gw (convexApproxSample x0 0 r ε x) := by
    simpa [gw, convexApproxSample] using
      (convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
        (u := fun y => u y - v y)
        hU hρ hx hball hr hε hεOne)
  rw [huRepresentative, hvRepresentative, hwRepresentative]
  rw [hconvSub]

theorem eLpNorm_sub_convexApproxSmoothing_le
    {d : ℕ} {U : Set (Vec d)}
    {ρ u v : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    (hpOne : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hu : MemLpOn U p u) (hv : MemLpOn U p v)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) ≤
      ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
          (1 / p).toReal *
        eLpNorm (fun x => u x - v x)
          p (volume.restrict U) := by
  have huv :
      MemLpOn U p (fun x => u x - v x) :=
    hu.sub hv
  calc
    eLpNorm
        (fun x =>
          convexApproxSmoothing ρ u x0 r ε x -
            convexApproxSmoothing ρ v x0 r ε x)
        p (volume.restrict U) =
      eLpNorm
        (convexApproxSmoothing ρ
          (fun y => u y - v y) x0 r ε)
        p (volume.restrict U) := by
      exact
        eLpNorm_congr_ae
          (convexApproxSmoothing_sub_ae_eq
            hU hρ hpOne hu hv
            hball hr hε hεOne).symm
    _ ≤
        ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / p).toReal *
          eLpNorm (fun x => u x - v x)
            p (volume.restrict U) :=
      eLpNorm_convexApproxSmoothing_le
        hU hρ hpOne hpTop huv hball hr hε hεOne

theorem integrableOn_comp_smul_add_of_pos
    {d : ℕ} {s : Set (Vec d)}
    {u : Vec d → ℝ} {a : ℝ} (ha : 0 < a)
    (b : Vec d) (hs : MeasurableSet s)
    (hu :
      IntegrableOn u (translateSet b (a • s)) volume) :
    IntegrableOn
      (fun x => u (a • x + b)) s volume := by
  have haNe : a ≠ 0 :=
    ha.ne'
  let V : Set (Vec d) :=
    translateSet b (a • s)
  have hVMeas : MeasurableSet V := by
    have hpre :
        ⇑(Homeomorph.subRight b) ⁻¹' (a • s) = V := by
      ext x
      simp [V, mem_translateSet_iff_sub_mem]
    rw [← hpre]
    exact
      ((Homeomorph.subRight b).toMeasurableEquiv.measurableSet_preimage).2
        (((Homeomorph.smulOfNeZero a haNe).toMeasurableEquiv.measurableSet_image).2
          hs)
  have hindicator :
      Integrable (Set.indicator V u) volume :=
    hu.integrable_indicator hVMeas
  have htranslated :
      Integrable
        (fun x => Set.indicator V u (x + b))
        volume := by
    exact
      (measurePreserving_add_right
        (volume : Measure (Vec d)) b
        ).integrable_comp_of_integrable hindicator
  have hscaled :
      Integrable
        (fun x => Set.indicator V u (a • x + b))
        volume := by
    let g : Vec d → ℝ :=
      fun x => Set.indicator V u (x + b)
    have hg : Integrable g volume := by
      simpa only [g] using htranslated
    simpa only [g, Function.comp_apply] using
      hg.comp_smul haNe
  have hindicatorEq :
      Set.indicator s (fun x => u (a • x + b)) =
        fun x => Set.indicator V u (a • x + b) := by
    funext x
    by_cases hx : x ∈ s
    · have hyV : a • x + b ∈ V := by
        exact
          ⟨a • x, Set.smul_mem_smul_set hx, rfl⟩
      simp [Set.indicator_of_mem, hx, hyV]
    · have hyV : a • x + b ∉ V := by
        intro hyV
        rcases hyV with ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with
          ⟨x', hx', rfl⟩
        have hxx : x = x' := by
          have h :=
            congrArg
              (fun t : Vec d => a⁻¹ • (t - b)) hyw
          simpa [smul_smul,
            inv_mul_cancel₀ haNe] using h
        exact hx (hxx ▸ hx')
      simp [Set.indicator_of_notMem, hx, hyV]
  refine (integrable_indicator_iff hs).1 ?_
  exact hindicatorEq ▸ hscaled

theorem integrableOn_comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : IntegrableOn u U volume)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε : 0 ≤ ε) (hεOne : ε < 1) :
    IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      U volume := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  let V : Set (Vec d) :=
    translateSet b (a • U)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo
        (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε (le_of_lt hεOne)
  have hVSub : V ⊆ U :=
    translateSet_smul_subset_of_convexApproxSample_mapsTo
      (x0 := x0) (z := z) (r := r) (ε := ε) hmap
  have huV : IntegrableOn u V volume :=
    hu.mono_set hVSub
  simpa only [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_of_pos
      (d := d) (u := u) (a := a) haPos b
      hU.isOpen.measurableSet huV)

theorem
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hKSub : K ⊆ U) (hKCompact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε : 0 ≤ ε) (hεOne : ε < 1) :
    IntegrableOn
      (fun x => u (convexApproxSample x0 z r ε x))
      K volume := by
  let a : ℝ :=
    1 - ε
  let b : Vec d :=
    ε • (x0 - r • z)
  let V : Set (Vec d) :=
    translateSet b (a • K)
  have haPos : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo
        (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε (le_of_lt hεOne)
  have hVSub : V ⊆ U := by
    intro y hy
    rcases hy with ⟨w, hw, hyw⟩
    rcases Set.mem_smul_set.mp hw with
      ⟨x, hx, rfl⟩
    have hxU : x ∈ U :=
      hKSub hx
    have hyU :
        convexApproxSample x0 z r ε x ∈ U :=
      hmap hxU
    rw [hyw]
    simpa only [convexApproxSample, a, b] using hyU
  have hVCompact : IsCompact V := by
    have himage :
        (fun x : Vec d => a • x + b) '' K = V := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        exact
          ⟨a • x, Set.smul_mem_smul_set hx, by simp⟩
      · intro hy
        rcases hy with ⟨w, hw, hyw⟩
        rcases Set.mem_smul_set.mp hw with
          ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp [hyw]
    rw [← himage]
    exact
      hKCompact.image
        ((continuous_id.const_smul a).add
          continuous_const)
  have huV : IntegrableOn u V volume :=
    hu.integrableOn_compact_subset hVSub hVCompact
  simpa only [convexApproxSample, a, b, V] using
    (integrableOn_comp_smul_add_of_pos
      (d := d) (u := u) (a := a) haPos b
      hKCompact.measurableSet huV)

theorem
    integrableOn_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ψ : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hψ : Continuous ψ)
    (hKSub : K ⊆ U) (hKCompact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε : 0 ≤ ε) (hεOne : ε < 1) :
    IntegrableOn
      (fun x =>
        Set.indicator U u
            (convexApproxSample x0 z r ε x) *
          ψ x)
      K volume := by
  have hcomp :
      IntegrableOn
        (fun x =>
          u (convexApproxSample x0 z r ε x))
        K volume :=
    integrableOn_comp_convexApproxSample_of_locallyIntegrableOn
      hU hu hKSub hKCompact hball hr hz hε hεOne
  have hmap :
      Set.MapsTo
        (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε (le_of_lt hεOne)
  have hmul :
      IntegrableOn
        (fun x =>
          u (convexApproxSample x0 z r ε x) * ψ x)
        K volume :=
    hcomp.mul_continuousOn
      hψ.continuousOn hKCompact
  rw [IntegrableOn] at hmul ⊢
  refine hmul.congr ?_
  filter_upwards
    [ae_restrict_mem hKCompact.measurableSet] with x hx
  rw [Set.indicator_of_mem (hmap (hKSub hx))]

theorem
    integrableOn_kernel_mul_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
    {d : ℕ} {U K : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u ρ ψ : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hψ : Continuous ψ)
    (hKSub : K ⊆ U) (hKCompact : IsCompact K)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε : 0 ≤ ε) (hεOne : ε < 1) :
    IntegrableOn
      (fun x =>
        ρ z *
          Set.indicator U u
            (convexApproxSample x0 z r ε x) *
          ψ x)
      K volume := by
  rw [IntegrableOn]
  simpa only [mul_assoc] using
    (integrableOn_indicator_comp_convexApproxSample_mul_of_locallyIntegrableOn
      hU hu hψ hKSub hKCompact
      hball hr hz hε hεOne).integrable.const_mul (ρ z)

end

end PDE
