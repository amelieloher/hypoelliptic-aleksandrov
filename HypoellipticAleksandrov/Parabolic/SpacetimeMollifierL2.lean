module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Translation input for spacetime mollification in `L²`

This module begins the `L²` approximation theory for the fixed spacetime
mollifier by connecting raw translations to the continuous translation action
on `Lp`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2

private theorem memLp_add_translate
    {d : ℕ} (x : TimeVelocity d)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    MemLp (fun z => f (x + z)) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  exact hf.comp_measurePreserving (measurePreserving_add_left volume x)

private theorem eLpNorm_add_translate
    {d : ℕ} (x : TimeVelocity d)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    eLpNorm (fun z => f (x + z)) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) =
      eLpNorm f (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) := by
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    (measurePreserving_add_left volume x)

private theorem tendsto_eLpNorm_add_translate_sub
    {d : ℕ}
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Tendsto
      (fun x : TimeVelocity d =>
        eLpNorm (fun z => f (x + z) - f z) (2 : ℝ≥0∞)
          (volume : Measure (TimeVelocity d)))
      (nhds 0) (nhds 0) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : ContinuousVAdd (TimeVelocity d)ᵈᵃᵃ
      (Lp ℝ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
  let F : Lp ℝ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) := hf.toLp f
  have hcont : Continuous (fun x : TimeVelocity d => DomAddAct.mk x +ᵥ F) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have hzero : DomAddAct.mk (0 : TimeVelocity d) +ᵥ F = F := by simp
  have hcontsub : Continuous
      (fun x : TimeVelocity d => (DomAddAct.mk x +ᵥ F) - F) :=
    hcont.sub (continuous_const : Continuous (fun _ : TimeVelocity d => F))
  have hsub : Tendsto
      (fun x : TimeVelocity d => (DomAddAct.mk x +ᵥ F) - F)
      (nhds 0) (nhds 0) := by
    have h : Tendsto
        (fun x : TimeVelocity d => (DomAddAct.mk x +ᵥ F) - F)
        (nhds 0)
        (nhds ((DomAddAct.mk (0 : TimeVelocity d) +ᵥ F) - F)) :=
      hcontsub.continuousAt
    simpa only [Function.comp_def, hzero, sub_self] using h
  have henorm : Tendsto
      (fun x : TimeVelocity d => ‖(DomAddAct.mk x +ᵥ F) - F‖ₑ)
      (nhds 0) (nhds 0) := by
    simpa only [enorm_zero] using hsub.enorm
  apply henorm.congr'
  filter_upwards with x
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  have hzf_add : (fun z : TimeVelocity d => F (x + z)) =ᵐ[volume]
      (fun z => f (x + z)) := by
    simpa only [Function.comp_def] using
      (quasiMeasurePreserving_add_left (volume : Measure (TimeVelocity d)) x).ae_eq_comp
        hf.coeFn_toLp
  filter_upwards [Lp.coeFn_sub (DomAddAct.mk x +ᵥ F) F,
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk x) F,
    hf.coeFn_toLp, hzf_add] with z hsubz hz hzf hzf_add_z
  rw [hsubz]
  change (DomAddAct.mk x +ᵥ F : TimeVelocity d → ℝ) z - F z =
    f (x + z) - f z
  rw [hz, hzf]
  change F (x + z) - f z = f (x + z) - f z
  rw [hzf_add_z]

private theorem spacetimeMollifier_integrable
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Integrable (spacetimeMollifier (d := d) ε)
      (volume : Measure (TimeVelocity d)) := by
  exact (spacetimeMollifier_contDiff (d := d) ε).continuous
    |>.integrable_of_hasCompactSupport (spacetimeMollifier_hasCompactSupport hε)

private theorem integrable_spacetimeMollifier_mul_sq_sub
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        spacetimeMollifier ε p.1 * f (p.2 - p.1) ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hprod : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        spacetimeMollifier ε p.1 * f p.2 ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    (spacetimeMollifier_integrable hε).mul_prod hf.integrable_sq
  simpa only [Function.comp_def] using
    (measurePreserving_prod_sub
      (volume : Measure (TimeVelocity d))
      (volume : Measure (TimeVelocity d))).integrable_comp_of_integrable hprod

private theorem integral_integral_spacetimeMollifier_mul_sq_sub_swap
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    (∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume ∂volume) =
      ∫ x : TimeVelocity d, ∫ z : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume ∂volume := by
  apply integral_integral_swap
  simpa only [Function.comp_def, Function.uncurry_def, Prod.swap] using
    (integrable_spacetimeMollifier_mul_sq_sub hε f hf).swap

private theorem ae_sq_integral_spacetimeMollifier_mul_le
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    ∀ᵐ z : TimeVelocity d ∂volume,
      |∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ∂volume| ^ 2 ≤
        ∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume := by
  have hsections :=
    (integrable_spacetimeMollifier_mul_sq_sub hε f hf).prod_left_ae
  filter_upwards [hsections] with z hz
  let a : TimeVelocity d → ℝ := fun x => Real.sqrt (spacetimeMollifier ε x)
  let b : TimeVelocity d → ℝ := fun x =>
    Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|
  have ha_cont : Continuous a :=
    (spacetimeMollifier_contDiff (d := d) ε).continuous.sqrt
  have ha_sq : Integrable (fun x => a x ^ 2)
      (volume : Measure (TimeVelocity d)) := by
    apply (spacetimeMollifier_integrable hε).congr
    exact ae_of_all _ fun x => by
      simp only [a, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
  have ha : MemLp a (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (memLp_two_iff_integrable_sq ha_cont.aestronglyMeasurable).2 ha_sq
  have hsub : MeasurePreserving (fun x : TimeVelocity d => z - x)
      (volume : Measure (TimeVelocity d)) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left (volume : Measure (TimeVelocity d)) z).comp
        (Measure.measurePreserving_neg (volume : Measure (TimeVelocity d)))
  have hb_meas : AEStronglyMeasurable b
      (volume : Measure (TimeVelocity d)) :=
    ha_cont.aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.comp_measurePreserving hsub).norm)
  have hb_sq : Integrable (fun x => b x ^ 2)
      (volume : Measure (TimeVelocity d)) := by
    convert hz using 1
    · funext x
      simp only [b, mul_pow, sq_abs, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
  have hb : MemLp b (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (memLp_two_iff_integrable_sq hb_meas).2 hb_sq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure (TimeVelocity d))) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun x => Real.sqrt_nonneg _)
    (ae_of_all _ fun x => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa only [ENNReal.ofReal_ofNat] using
      ha) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hholder' :
      (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * |f (z - x)| ∂volume) ≤
        Real.sqrt (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume) := by
    calc
      _ = ∫ x : TimeVelocity d,
          Real.sqrt (spacetimeMollifier ε x) *
            (Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|) ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change spacetimeMollifier ε x * |f (z - x)| =
            Real.sqrt (spacetimeMollifier ε x) *
              (Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|)
          rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]
      _ ≤ _ := hholder
      _ = _ := by
        have hone : (∫ x : TimeVelocity d,
            Real.sqrt (spacetimeMollifier ε x) ^ 2 ∂volume) = 1 := by
          calc
            _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x ∂volume := by
              apply integral_congr_ae
              exact ae_of_all _ fun x => Real.sq_sqrt (spacetimeMollifier_nonneg ε x)
            _ = 1 := spacetimeMollifier_integral hε
        have htwo : (∫ x : TimeVelocity d,
            Real.sqrt (spacetimeMollifier ε x) ^ 2 * f (z - x) ^ 2 ∂volume) =
            ∫ x : TimeVelocity d,
              spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change Real.sqrt (spacetimeMollifier ε x) ^ 2 * f (z - x) ^ 2 =
              spacetimeMollifier ε x * f (z - x) ^ 2
            rw [Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
        rw [hone, htwo, Real.one_rpow, one_mul, Real.sqrt_eq_rpow]
        congr 2
        norm_num
  have habs :
      |∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ∂volume| ≤
        (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume) ^ (2 : ℝ)⁻¹ := by
    calc
      |∫ x : TimeVelocity d, spacetimeMollifier ε x * f (z - x) ∂volume| =
          ‖∫ x : TimeVelocity d, spacetimeMollifier ε x * f (z - x) ∂volume‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : TimeVelocity d,
          ‖spacetimeMollifier ε x * f (z - x)‖ ∂volume :=
        norm_integral_le_integral_norm _
      _ = ∫ x : TimeVelocity d,
          spacetimeMollifier ε x * |f (z - x)| ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change |spacetimeMollifier ε x * f (z - x)| =
            spacetimeMollifier ε x * |f (z - x)|
          rw [abs_mul,
            abs_of_nonneg (spacetimeMollifier_nonneg ε x)]
      _ ≤ _ := by simpa only [Function.comp_def, Real.sqrt_eq_rpow, one_div] using hholder'
  have hright : 0 ≤ ∫ x : TimeVelocity d,
      spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume :=
    integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x) (sq_nonneg _)
  have habs' : |∫ x : TimeVelocity d,
      spacetimeMollifier ε x * f (z - x) ∂volume| ≤
      Real.sqrt (∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow, one_div] using habs
  have hsqrt_nonneg : 0 ≤ Real.sqrt (∫ x : TimeVelocity d,
      spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume) := Real.sqrt_nonneg _
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hsqrt_nonneg).2 habs'
  simpa only [Function.comp_def, Real.sq_sqrt hright] using hsquare

private theorem integral_integral_spacetimeMollifier_mul_sq_sub
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    (∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume ∂volume) =
      ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
  rw [integral_integral_spacetimeMollifier_mul_sq_sub_swap hε f hf]
  have htranslate (x : TimeVelocity d) :
      (∫ z : TimeVelocity d, f (z - x) ^ 2 ∂volume) =
        ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
    have hsub : MeasurePreserving (MeasurableEquiv.addLeft (-x : TimeVelocity d))
        (volume : Measure (TimeVelocity d)) volume := by
      exact measurePreserving_add_left (volume : Measure (TimeVelocity d)) (-x)
    simpa [sub_eq_add_neg, add_comm] using
      hsub.integral_comp' (fun z => f z ^ 2)
  simp_rw [integral_const_mul, htranslate]
  rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]

/-- Positive-radius spacetime mollification is an exact `L²` contraction. -/
theorem eLpNorm_spacetimeMollification_le
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    eLpNorm (spacetimeMollification ε f) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) ≤
      eLpNorm f (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) := by
  have hcont : Continuous (spacetimeMollification ε f) :=
    (contDiff_spacetimeMollification hε f (hf.locallyIntegrable (by norm_num))).continuous
  have hweighted : Integrable (fun z : TimeVelocity d =>
      ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume)
      (volume : Measure (TimeVelocity d)) := by
    simpa only [Function.comp_def, Function.uncurry_def, Prod.swap] using
      (integrable_spacetimeMollifier_mul_sq_sub hε f hf).swap.integral_prod_left
  have hsquare : Integrable (fun z : TimeVelocity d =>
      spacetimeMollification ε f z ^ 2)
      (volume : Measure (TimeVelocity d)) := by
    apply hweighted.mono' (hcont.aestronglyMeasurable.pow 2)
    filter_upwards [ae_sq_integral_spacetimeMollifier_mul_le hε f hf] with z hz
    rw [Pi.pow_apply, Real.norm_eq_abs, abs_sq]
    simpa only [Function.comp_def, spacetimeMollification, convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, sq_abs] using hz
  have hg : MemLp (spacetimeMollification ε f) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hsquare
  have hintegral :
      (∫ z : TimeVelocity d, spacetimeMollification ε f z ^ 2 ∂volume) ≤
        ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
    calc
      _ ≤ ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2 ∂volume ∂volume := by
        apply integral_mono_ae hsquare hweighted
        filter_upwards [ae_sq_integral_spacetimeMollifier_mul_le hε f hf] with z hz
        simpa only [Function.comp_def, spacetimeMollification, convolution_def,
          ContinuousLinearMap.lsmul_apply, smul_eq_mul, sq_abs] using hz
      _ = _ := integral_integral_spacetimeMollifier_mul_sq_sub hε f hf
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  apply ENNReal.ofReal_le_ofReal
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hintegral (by norm_num)

/-- Positive-radius spacetime mollification preserves global `L²`
membership. -/
theorem spacetimeMollification_memLp
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    MemLp (spacetimeMollification ε f) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  exact (eLpNorm_spacetimeMollification_le hε f hf).trans_lt hf.eLpNorm_lt_top

private theorem integrable_spacetimeMollifier_mul_sq_sub_self
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        spacetimeMollifier ε p.1 * (f (p.2 - p.1) - f p.2) ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hfirst := (integrable_spacetimeMollifier_mul_sq_sub hε f hf).const_mul 2
  have hsecond : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        2 * spacetimeMollifier ε p.1 * f p.2 ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    simpa only [Function.comp_def, mul_assoc] using
      ((spacetimeMollifier_integrable hε).const_mul 2).mul_prod hf.integrable_sq
  apply (hfirst.add hsecond).mono'
  · have hz : AEStronglyMeasurable
        (fun p : TimeVelocity d × TimeVelocity d => f p.2)
        ((volume : Measure (TimeVelocity d)).prod volume) :=
      hf.aestronglyMeasurable.comp_snd
    have hsub : AEStronglyMeasurable
        (fun p : TimeVelocity d × TimeVelocity d => f (p.2 - p.1))
        ((volume : Measure (TimeVelocity d)).prod volume) := by
      simpa only [Function.comp_def] using hz.comp_measurePreserving
        (measurePreserving_prod_sub
          (volume : Measure (TimeVelocity d))
          (volume : Measure (TimeVelocity d)))
    exact ((spacetimeMollifier_contDiff (d := d) ε).continuous.comp continuous_fst
      |>.aestronglyMeasurable).mul ((hsub.sub hz).pow 2)
  · exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (spacetimeMollifier_nonneg ε p.1), abs_sq, Pi.add_apply]
      have hρ := spacetimeMollifier_nonneg ε p.1
      nlinarith [sq_nonneg (f (p.2 - p.1) + f p.2),
        sq_nonneg (f (p.2 - p.1) - f p.2)]

private theorem tendsto_eLpNorm_sub_translate_sub
    {d : ℕ}
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Tendsto
      (fun x : TimeVelocity d =>
        eLpNorm (fun z => f (z - x) - f z) (2 : ℝ≥0∞)
          (volume : Measure (TimeVelocity d)))
      (nhds 0) (nhds 0) := by
  have hneg : Tendsto (fun x : TimeVelocity d => -x) (nhds 0) (nhds 0) := by
    have hn := continuousAt_neg (G := TimeVelocity d) (x := (0 : TimeVelocity d))
    change Tendsto (fun x : TimeVelocity d => -x) (nhds 0) (nhds (-0)) at hn
    simpa only [Function.comp_def, neg_zero] using hn
  have h := (tendsto_eLpNorm_add_translate_sub f hf).comp hneg
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h

private theorem integral_sq_sub_translate_eq_toReal_eLpNorm_sq
    {d : ℕ} (x : TimeVelocity d)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) =
      (eLpNorm (fun z => f (z - x) - f z) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d))).toReal ^ 2 := by
  have hsub : MeasurePreserving (fun z : TimeVelocity d => z - x)
      (volume : Measure (TimeVelocity d)) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left (volume : Measure (TimeVelocity d)) (-x))
  have hd : MemLp (fun z => f (z - x) - f z) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (hf.comp_measurePreserving hsub).sub hf
  rw [hd.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _),
    ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

private theorem tendsto_integral_sq_sub_translate
    {d : ℕ}
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Tendsto (fun x : TimeVelocity d =>
      ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume)
      (nhds 0) (nhds 0) := by
  have hfinite (x : TimeVelocity d) :
      eLpNorm (fun z => f (z - x) - f z) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) ≠ ∞ := by
    have hsub : MeasurePreserving (fun z : TimeVelocity d => z - x)
        (volume : Measure (TimeVelocity d)) volume := by
      simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
        measurePreserving_add_left (volume : Measure (TimeVelocity d)) (-x)
    exact ((hf.comp_measurePreserving hsub).sub hf).eLpNorm_ne_top
  have hreal : Tendsto (fun x : TimeVelocity d =>
      (eLpNorm (fun z => f (z - x) - f z) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d))).toReal) (nhds 0) (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfinite).2 (tendsto_eLpNorm_sub_translate_sub f hf)
  simpa only [Function.comp_def, integral_sq_sub_translate_eq_toReal_eLpNorm_sq (f := f) (hf := hf),
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    hreal.pow 2

private theorem ae_sq_integral_spacetimeMollifier_mul_sub_self_le
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    ∀ᵐ z : TimeVelocity d ∂volume,
      Integrable (fun x : TimeVelocity d => spacetimeMollifier ε x *
          (f (z - x) - f z)) volume ∧
        |∫ x : TimeVelocity d, spacetimeMollifier ε x *
            (f (z - x) - f z) ∂volume| ^ 2 ≤
          ∫ x : TimeVelocity d, spacetimeMollifier ε x *
            (f (z - x) - f z) ^ 2 ∂volume := by
  have hsections :=
    (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).prod_left_ae
  filter_upwards [hsections] with z hz
  let a : TimeVelocity d → ℝ := fun x => Real.sqrt (spacetimeMollifier ε x)
  let b : TimeVelocity d → ℝ := fun x =>
    Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|
  have ha_cont : Continuous a :=
    (spacetimeMollifier_contDiff (d := d) ε).continuous.sqrt
  have ha_sq : Integrable (fun x => a x ^ 2)
      (volume : Measure (TimeVelocity d)) := by
    apply (spacetimeMollifier_integrable hε).congr
    exact ae_of_all _ fun x => by
      simp only [a, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
  have ha : MemLp a (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (memLp_two_iff_integrable_sq ha_cont.aestronglyMeasurable).2 ha_sq
  have hsub : MeasurePreserving (fun x : TimeVelocity d => z - x)
      (volume : Measure (TimeVelocity d)) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure (TimeVelocity d)) z).comp
        (Measure.measurePreserving_neg (volume : Measure (TimeVelocity d)))
  have hb_meas : AEStronglyMeasurable b
      (volume : Measure (TimeVelocity d)) :=
    ha_cont.aestronglyMeasurable.mul
      (((hf.aestronglyMeasurable.comp_measurePreserving hsub).sub
        (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _ : TimeVelocity d => f z) volume)).norm)
  have hb_sq : Integrable (fun x => b x ^ 2)
      (volume : Measure (TimeVelocity d)) := by
    convert hz using 1
    · funext x
      simp only [b, mul_pow, sq_abs, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
  have hb : MemLp b (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    (memLp_two_iff_integrable_sq hb_meas).2 hb_sq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure (TimeVelocity d))) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => Real.sqrt_nonneg _)
    (ae_of_all _ fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa only [ENNReal.ofReal_ofNat] using
      ha) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hone : (∫ x : TimeVelocity d,
      Real.sqrt (spacetimeMollifier ε x) ^ 2 ∂volume) = 1 := by
    calc
      _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => Real.sq_sqrt (spacetimeMollifier_nonneg ε x)
      _ = 1 := spacetimeMollifier_integral hε
  have htwo : (∫ x : TimeVelocity d,
      Real.sqrt (spacetimeMollifier ε x) ^ 2 * (f (z - x) - f z) ^ 2 ∂volume) =
      ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * (f (z - x) - f z) ^ 2 ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change Real.sqrt (spacetimeMollifier ε x) ^ 2 * (f (z - x) - f z) ^ 2 =
        spacetimeMollifier ε x * (f (z - x) - f z) ^ 2
      rw [Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
  have habs : |∫ x : TimeVelocity d, spacetimeMollifier ε x *
      (f (z - x) - f z) ∂volume| ≤
      Real.sqrt (∫ x : TimeVelocity d, spacetimeMollifier ε x *
        (f (z - x) - f z) ^ 2 ∂volume) := by
    calc
      _ = ‖∫ x : TimeVelocity d, spacetimeMollifier ε x *
          (f (z - x) - f z) ∂volume‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : TimeVelocity d, ‖spacetimeMollifier ε x *
          (f (z - x) - f z)‖ ∂volume := norm_integral_le_integral_norm _
      _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
          |f (z - x) - f z| ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change |spacetimeMollifier ε x * (f (z - x) - f z)| =
            spacetimeMollifier ε x * |f (z - x) - f z|
          rw [abs_mul,
            abs_of_nonneg (spacetimeMollifier_nonneg ε x)]
      _ = ∫ x : TimeVelocity d, Real.sqrt (spacetimeMollifier ε x) *
          (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|) ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change spacetimeMollifier ε x * |f (z - x) - f z| =
            Real.sqrt (spacetimeMollifier ε x) *
              (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|)
          rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]
      _ ≤ _ := hholder
      _ = _ := by
        rw [hone, htwo, Real.one_rpow, one_mul, Real.sqrt_eq_rpow]
        congr 2
        norm_num
  have hright : 0 ≤ ∫ x : TimeVelocity d, spacetimeMollifier ε x *
      (f (z - x) - f z) ^ 2 ∂volume :=
    integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x) (sq_nonneg _)
  have hsquare := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 habs
  have habint : Integrable (fun x : TimeVelocity d =>
      spacetimeMollifier ε x * |f (z - x) - f z|) volume := by
    convert ha.integrable_mul hb using 1
    funext x
    simp only [a, b]
    change spacetimeMollifier ε x * |f (z - x) - f z| =
      Real.sqrt (spacetimeMollifier ε x) *
        (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|)
    rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]
  have hdiff : Integrable (fun x : TimeVelocity d =>
      spacetimeMollifier ε x * (f (z - x) - f z)) volume := by
    apply habint.mono' ((spacetimeMollifier_contDiff (d := d) ε).continuous
      |>.aestronglyMeasurable.mul
        (((hf.aestronglyMeasurable.comp_measurePreserving hsub).sub
          (aestronglyMeasurable_const : AEStronglyMeasurable
            (fun _ : TimeVelocity d => f z) volume))))
    exact ae_of_all _ fun x => by
      change |spacetimeMollifier ε x * (f (z - x) - f z)| ≤
        spacetimeMollifier ε x * |f (z - x) - f z|
      rw [abs_mul,
        abs_of_nonneg (spacetimeMollifier_nonneg ε x)]
  exact ⟨hdiff, by simpa only [Function.comp_def, Real.sq_sqrt hright] using hsquare⟩

private theorem tendsto_weighted_integral_sq_sub_translate
    {d : ℕ}
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Tendsto (fun ε : ℝ => ∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) ∂volume)
      (𝓝[>] 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hsmall := (tendsto_integral_sq_sub_translate f hf).eventually
    (Metric.ball_mem_nhds 0 (half_pos hδ))
  rcases Metric.mem_nhds_iff.1 hsmall with ⟨r, hr, hrball⟩
  have hepslt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hepslt] with ε hεpos hεr
  have hε : 0 < ε := hεpos
  have hmain : (∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) ∂volume) ≤ δ / 2 := by
    have hleft : Integrable (fun x : TimeVelocity d =>
        spacetimeMollifier ε x *
          (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume)) volume := by
      apply (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).integral_prod_left.congr
      exact ae_of_all _ fun x => by
        change (∫ y : TimeVelocity d, spacetimeMollifier ε x *
          (f (y - x) - f y) ^ 2 ∂volume) =
            spacetimeMollifier ε x *
              ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume
        rw [integral_const_mul]
    have hright : Integrable (fun x : TimeVelocity d =>
        spacetimeMollifier ε x * (δ / 2)) volume :=
      (spacetimeMollifier_integrable hε).mul_const (δ / 2)
    calc
      _ ≤ ∫ x : TimeVelocity d, spacetimeMollifier ε x * (δ / 2) ∂volume := by
        apply integral_mono hleft hright
        intro x
        by_cases hx : x ∈ Metric.ball (0 : TimeVelocity d) ε
        · have hxr : x ∈ Metric.ball (0 : TimeVelocity d) r :=
            (Metric.ball_subset_ball hεr.le) hx
          have hs := hrball hxr
          change dist (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) 0 <
            δ / 2 at hs
          rw [Real.dist_eq, sub_zero] at hs
          have hsnonneg : 0 ≤ ∫ z : TimeVelocity d,
              (f (z - x) - f z) ^ 2 ∂volume := integral_nonneg fun _ => sq_nonneg _
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hs.le)
            (spacetimeMollifier_nonneg ε x)
        · have hzero : spacetimeMollifier ε x = 0 :=
            Function.notMem_support.mp (by
              rw [spacetimeMollifier_support hε]
              exact hx)
          simpa only [Function.comp_def, hzero, zero_mul] using (le_refl (0 : ℝ))
      _ = δ / 2 := by
        rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]
  have hnonneg : 0 ≤ ∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) ∂volume :=
    integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x)
      (integral_nonneg fun _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hmain.trans_lt (half_lt_self hδ)

/-- Spacetime mollification converges strongly in global `L²` as the positive
radius tends to zero. -/
theorem tendsto_eLpNorm_spacetimeMollification_sub
    {d : ℕ}
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (spacetimeMollification ε f - f)
          (2 : ℝ≥0∞)
          (volume : Measure (TimeVelocity d)))
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ → ℝ := fun ε => ∫ z : TimeVelocity d,
    (spacetimeMollification ε f z - f z) ^ 2 ∂volume
  have hq : Tendsto q (𝓝[>] 0) (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun ε => integral_nonneg fun _ => sq_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hg := (spacetimeMollification_memLp hε f hf).sub hf
      have hright : Integrable (fun z : TimeVelocity d =>
            ∫ x : TimeVelocity d, spacetimeMollifier ε x *
              (f (z - x) - f z) ^ 2 ∂volume) volume :=
          (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).integral_prod_right
      calc
        q ε ≤ ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
              spacetimeMollifier ε x * (f (z - x) - f z) ^ 2 ∂volume ∂volume := by
            apply integral_mono_ae hg.integrable_sq hright
            filter_upwards [ae_sq_integral_spacetimeMollifier_mul_sub_self_le hε f hf]
              with z hz
            have hconst : Integrable (fun x : TimeVelocity d =>
                spacetimeMollifier ε x * f z) volume :=
              (spacetimeMollifier_integrable hε).mul_const (f z)
            have htrans : Integrable (fun x : TimeVelocity d =>
                spacetimeMollifier ε x * f (z - x)) volume := by
              apply (hz.1.add hconst).congr
              exact ae_of_all _ fun x => by
                change spacetimeMollifier ε x * (f (z - x) - f z) +
                    spacetimeMollifier ε x * f z = spacetimeMollifier ε x * f (z - x)
                ring
            have hid : spacetimeMollification ε f z - f z =
                ∫ x : TimeVelocity d, spacetimeMollifier ε x *
                  (f (z - x) - f z) ∂volume := by
              calc
                _ = (∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    f (z - x) ∂volume) - f z := by
                  rw [spacetimeMollification, convolution_def]
                  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
                _ = (∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    f (z - x) ∂volume) -
                    ∫ x : TimeVelocity d, spacetimeMollifier ε x * f z ∂volume := by
                  rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]
                _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    (f (z - x) - f z) ∂volume := by
                  rw [← integral_sub htrans hconst]
                  apply integral_congr_ae
                  exact ae_of_all _ fun x => by ring
            simpa only [Function.comp_def, q, Pi.sub_apply, hid, sq_abs] using hz.2
        _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
              (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume) ∂volume := by
            rw [integral_integral_swap (by
              simpa only [Function.comp_def, Function.uncurry_def, Prod.swap] using
                (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).swap)]
            apply integral_congr_ae
            exact ae_of_all _ fun x => by
              change (∫ z : TimeVelocity d, spacetimeMollifier ε x *
                (f (z - x) - f z) ^ 2 ∂volume) =
                  spacetimeMollifier ε x *
                    ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2 ∂volume
              rw [integral_const_mul]
    · exact tendsto_weighted_integral_sq_sub_translate f hf
  have hrpow : Tendsto (fun ε => (q ε) ^ (1 / (2 : ℝ))) (𝓝[>] 0) (nhds 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      hq.rpow_const (Or.inr (by norm_num : 0 ≤ (1 / (2 : ℝ))))
  have hofReal : Tendsto (fun ε => ENNReal.ofReal ((q ε) ^ (1 / (2 : ℝ))))
      (𝓝[>] 0) (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrpow
  apply hofReal.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hg := (spacetimeMollification_memLp hε f hf).sub hf
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  congr 2
  · apply integral_congr_ae
    exact ae_of_all _ fun z => by
      simp only [Pi.sub_apply, ENNReal.toReal_ofNat, Real.norm_eq_abs,
        Real.rpow_two, sq_abs]
  · norm_num

/-- Strong spacetime-mollification convergence persists on every restricted
carrier. -/
theorem tendsto_eLpNorm_spacetimeMollification_sub_restrict
    {d : ℕ}
    (V : Set (TimeVelocity d))
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (spacetimeMollification ε f - f)
          (2 : ℝ≥0∞)
          ((volume : Measure (TimeVelocity d)).restrict V))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (tendsto_eLpNorm_spacetimeMollification_sub f hf)
    (Eventually.of_forall fun _ => bot_le)
    (Eventually.of_forall fun ε =>
      eLpNorm_mono_measure (spacetimeMollification ε f - f)
        Measure.restrict_le_self)

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
