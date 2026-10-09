module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# One-sided reverse-time Bochner averages

This module provides literal reverse-time Bochner Steklov windows and their
basic regularity.  The local strong approximation assertions are stated on
strictly interior compact intervals, so they remain assertions about `Lp`
classes rather than selected pointwise representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Forward literal reverse-time Bochner Steklov window average. -/
noncomputable def reverseTimeForwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc t (t + h), f s ∂reverseTimeVolume T

/-- Backward literal reverse-time Bochner Steklov window average. -/
noncomputable def reverseTimeBackwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc (t - h) t, f s ∂reverseTimeVolume T

private theorem reverseTimeVolume_isFiniteMeasure (T : ℝ) :
    IsFiniteMeasure (reverseTimeVolume T) := by
  unfold reverseTimeVolume reverseTimeOpenInterval
  infer_instance

private theorem reverseTimeVolume_noAtoms (T : ℝ) :
    NoAtoms (reverseTimeVolume T) := by
  change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
  infer_instance

private theorem forward_window_product_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ) :
    MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) := by
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := by
    dsimp only [μs]
    infer_instance
  let hzero : MemLp (fun z : ℝ × ℝ => F z.2) (2 : ℝ≥0∞) (μs.prod volume) :=
    hF.comp_snd μs
  let hshear : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      (μs.prod volume) (μs.prod volume) :=
    measurePreserving_prod_add μs volume
  let hplus : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2)) (2 : ℝ≥0∞)
      (μs.prod volume) := by
    simpa only [Function.comp_def] using hzero.comp_measurePreserving hshear
  have hzeroK : MemLp (fun z : ℝ × ℝ => F z.2) (2 : ℝ≥0∞) (μs.prod μt) := by
    simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
      hzero.restrict (univ ×ˢ K)
  have hplusK : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2)) (2 : ℝ≥0∞) (μs.prod μt) := by
    simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
      hplus.restrict (univ ×ˢ K)
  exact hplusK.sub hzeroK

private theorem forward_window_product_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    Integrable (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
  (forward_window_product_memLp F hF h K).integrable (by norm_num)

private theorem forward_window_sqNorm_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (s + t) - F t‖ ^ 2 := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    forward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  simpa only [MeasureTheory.integral] using
    integral_integral_swap hPhiSq

private theorem ae_integrable_forward_window_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      Integrable (fun s => F (s + t) - F t) (volume.restrict (Ioc 0 h)) := by
  exact (forward_window_product_integrable F hF h K).prod_left_ae

private theorem ae_memLp_forward_window_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (s + t) - F t) (2 : ℝ≥0∞)
        (volume.restrict (Ioc 0 h)) := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    forward_window_product_memLp F hF h K
  have hPhiInt : Integrable (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable (by norm_num)
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  filter_upwards [hPhiInt.prod_left_ae, hPhiSq.prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem sqNorm_smul_window_integral_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℝ) (hh : 0 < h) (φ : ℝ → E)
    (hφ : MemLp φ (2 : ℝ≥0∞) (volume.restrict (Ioc 0 h))) :
    ‖h⁻¹ • ∫ s, φ s ∂volume.restrict (Ioc 0 h)‖ ^ 2 ≤
      h⁻¹ * ∫ s, ‖φ s‖ ^ 2 ∂volume.restrict (Ioc 0 h) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 h)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun s => ‖φ s‖) (g := fun _ => (1 : ℝ))
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => zero_le_one)
    (by simpa only [ENNReal.ofReal_ofNat] using hφ.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using
      (memLp_const (1 : ℝ) : MemLp _ (2 : ℝ≥0∞) μ))
  have hvol : μ.real univ = h := by
    dsimp only [μ]
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
  have hB : 0 ≤ ∫ s, ‖φ s‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hA : 0 ≤ ∫ s, ‖φ s‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hholder' : ∫ s, ‖φ s‖ ∂μ ≤
      (∫ s, ‖φ s‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ _s, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_one] using hholder
  have hholder'' : ∫ s, ‖φ s‖ ∂μ ≤
      √(∫ s, ‖φ s‖ ^ 2 ∂μ) * √h := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two, integral_const, hvol, one_smul, smul_eq_mul,
      Real.one_rpow, one_pow, mul_one] using hholder'
  have hmain : (h⁻¹ * ∫ s, ‖φ s‖ ∂μ) ^ 2 ≤
      (h⁻¹ * (√(∫ s, ‖φ s‖ ^ 2 ∂μ) * √h)) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hh.le) hA)
      (mul_le_mul_of_nonneg_left hholder'' (inv_nonneg.mpr hh.le)) 2
  have hcalc : (h⁻¹ * (√(∫ s, ‖φ s‖ ^ 2 ∂μ) * √h)) ^ 2 =
      h⁻¹ * ∫ s, ‖φ s‖ ^ 2 ∂μ := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hh.le]
    field_simp [ne_of_gt hh]
  calc
    ‖h⁻¹ • ∫ s, φ s ∂μ‖ ^ 2 = (h⁻¹ * ‖∫ s, φ s ∂μ‖) ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
    _ ≤ (h⁻¹ * ∫ s, ‖φ s‖ ∂μ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hh.le) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm φ)
          (inv_nonneg.mpr hh.le)) 2
    _ ≤ (h⁻¹ * (√(∫ s, ‖φ s‖ ^ 2 ∂μ) * √h)) ^ 2 := hmain
    _ = h⁻¹ * ∫ s, ‖φ s‖ ^ 2 ∂μ := hcalc

private theorem sqNorm_forward_window_average_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (hh : 0 < h) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2) ≤
      h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 := by
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := by
    dsimp only [μs]
    infer_instance
  letI : IsFiniteMeasure μt := by
    exact inferInstance
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      (μs.prod μt) := by
    simpa only [μs, μt] using forward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      (μs.prod μt) := hPhi.integrable_norm_pow (by norm_num)
  have hright : Integrable (fun t => h⁻¹ *
      ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs) μt :=
    (hPhiSq.integral_prod_right).const_mul _
  have hslice : ∀ᵐ t ∂μt,
      MemLp (fun s => F (s + t) - F t) (2 : ℝ≥0∞) μs := by
    simpa only [μs, μt] using ae_memLp_forward_window_slice F hF h K
  have hbound : (∫ t, ‖h⁻¹ • ∫ s, F (s + t) - F t ∂μs‖ ^ 2 ∂μt) ≤
      ∫ t, h⁻¹ * ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      hright
    filter_upwards [hslice] with t ht
    exact sqNorm_smul_window_integral_le h hh _ ht
  calc
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2) =
        ∫ t, ‖h⁻¹ • ∫ s, F (s + t) - F t ∂μs‖ ^ 2 ∂μt := rfl
    _ ≤ ∫ t, h⁻¹ * ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := hbound
    _ = h⁻¹ * ∫ t, ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := by
      rw [integral_const_mul]
    _ = h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 := by
      rw [← forward_window_sqNorm_integral_swap F hF h K]

private theorem backward_window_product_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ) :
    MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) := by
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := by
    dsimp only [μs]
    infer_instance
  let hzero : MemLp (fun z : ℝ × ℝ => F z.2) (2 : ℝ≥0∞) (μs.prod volume) :=
    hF.comp_snd μs
  let hshear : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 - z.1))
      (μs.prod volume) (μs.prod volume) :=
    measurePreserving_prod_sub μs volume
  let hminus : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1)) (2 : ℝ≥0∞)
      (μs.prod volume) := by
    simpa only [Function.comp_def] using hzero.comp_measurePreserving hshear
  have hzeroK : MemLp (fun z : ℝ × ℝ => F z.2) (2 : ℝ≥0∞) (μs.prod μt) := by
    simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
      hzero.restrict (univ ×ˢ K)
  have hminusK : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1)) (2 : ℝ≥0∞)
      (μs.prod μt) := by
    simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
      hminus.restrict (univ ×ˢ K)
  exact hminusK.sub hzeroK

private theorem backward_window_product_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    Integrable (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
  (backward_window_product_memLp F hF h K).integrable (by norm_num)

private theorem backward_window_sqNorm_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (t - s) - F t‖ ^ 2 := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    backward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  simpa only [MeasureTheory.integral] using integral_integral_swap hPhiSq

private theorem ae_memLp_backward_window_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (t - s) - F t) (2 : ℝ≥0∞) (volume.restrict (Ioc 0 h)) := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    backward_window_product_memLp F hF h K
  have hPhiInt : Integrable (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable (by norm_num)
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  filter_upwards [hPhiInt.prod_left_ae, hPhiSq.prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem sqNorm_backward_window_average_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (hh : 0 < h) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2) ≤
      h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 := by
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := by
    dsimp only [μs]
    infer_instance
  letI : IsFiniteMeasure μt := by exact inferInstance
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      (μs.prod μt) := by
    simpa only [μs, μt] using backward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      (μs.prod μt) := hPhi.integrable_norm_pow (by norm_num)
  have hright : Integrable (fun t => h⁻¹ *
      ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs) μt :=
    (hPhiSq.integral_prod_right).const_mul _
  have hslice : ∀ᵐ t ∂μt,
      MemLp (fun s => F (t - s) - F t) (2 : ℝ≥0∞) μs := by
    simpa only [μs, μt] using ae_memLp_backward_window_slice F hF h K
  have hbound : (∫ t, ‖h⁻¹ • ∫ s, F (t - s) - F t ∂μs‖ ^ 2 ∂μt) ≤
      ∫ t, h⁻¹ * ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hright
    filter_upwards [hslice] with t ht
    exact sqNorm_smul_window_integral_le h hh _ ht
  calc
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2) =
        ∫ t, ‖h⁻¹ • ∫ s, F (t - s) - F t ∂μs‖ ^ 2 ∂μt := rfl
    _ ≤ ∫ t, h⁻¹ * ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := hbound
    _ = h⁻¹ * ∫ t, ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := by
      rw [integral_const_mul]
    _ = h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 := by
      rw [← backward_window_sqNorm_integral_swap F hF h K]

private theorem forwardSteklov_eq_primitive_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeForwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  have hadd : (∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) +
      ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      ∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T :=
    intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
  have hsub : ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      (∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hadd)
  rw [reverseTimeForwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

private theorem tendsto_inv_mul_setIntegral_Ioc_zero
    (q : ℝ → ℝ) (hq : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hq0 : ∀ s, 0 ≤ q s) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ s in Ioc 0 h, q s) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin] with h hh
    exact hc.trans_le (mul_nonneg (inv_nonneg.mpr hh.le)
      (integral_nonneg fun s => hq0 s))
  · intro ε hε
    have hqhalf : ∀ᶠ s : ℝ in 𝓝[>] 0, q s < ε / 2 :=
      hq.eventually (eventually_lt_nhds (half_pos hε))
    rcases mem_nhdsGT_iff_exists_Ioc_subset.mp hqhalf with ⟨δ, hδ, hδq⟩
    filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    have hI : (∫ s in Ioc 0 h, q s) ≤ ∫ _s in Ioc 0 h, ε / 2 := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun s => hq0 s
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact (hδq ⟨hs.1, hs.2.trans hh.2⟩).le
    have hconst : (∫ _s in Ioc 0 h, ε / 2) = h * (ε / 2) := by
      rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hh.1.le, sub_zero, smul_eq_mul]
    calc
      h⁻¹ * ∫ s in Ioc 0 h, q s ≤ h⁻¹ * (h * (ε / 2)) :=
        mul_le_mul_of_nonneg_left (hI.trans_eq hconst) (inv_nonneg.mpr hh.1.le)
      _ = ε / 2 := by field_simp [ne_of_gt hh.1]
      _ < ε := half_lt_self hε

private theorem forwardSteklov_sub_eq_forward_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h a b : ℝ) (hh : 0 < h) (hhT : h < T - b) (ha : 0 < a) (hb : b < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Icc a b) :
    reverseTimeForwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (s + t) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let W : Set ℝ := Ioc t (t + h)
  have hwin : W ⊆ S := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le ha (ht.1.trans hx.1.le)
    · calc
        x ≤ t + h := hx.2
        _ ≤ b + h := by simpa only [add_comm] using add_le_add_right ht.2 h
        _ < T := by linarith
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict_of_subset hwin]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [F, Set.indicator_of_mem (hwin hx)]
  have hshift : (∫ s in Ioc 0 h, F (s + t)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (s + t)) = ∫ s in (0 : ℝ)..h, F (s + t) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in (0 : ℝ) + t..h + t, F x :=
        intervalIntegral.integral_comp_add_right F t
      _ = ∫ x in t..t + h, F x := by simp only [zero_add, add_comm h t]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    simp only [F, Set.indicator_of_mem htS]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    exact one_smul _ _
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (s + t)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (measurePreserving_add_right volume t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeForwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem backwardSteklov_sub_eq_backward_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h a b : ℝ) (hh : 0 < h) (hhA : h < a) (ha : 0 < a) (hb : b < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Icc a b) :
    reverseTimeBackwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (t - s) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let W : Set ℝ := Ioc (t - h) t
  have hwin : W ⊆ S := by
    intro x hx
    constructor
    · exact (sub_pos.mpr (hhA.trans_le ht.1)).trans hx.1
    · exact lt_of_le_of_lt hx.2 (ht.2.trans_lt hb)
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict_of_subset hwin]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [F, Set.indicator_of_mem (hwin hx)]
  have hshift : (∫ s in Ioc 0 h, F (t - s)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (t - s)) = ∫ s in (0 : ℝ)..h, F (t - s) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in t - h..t - 0, F x := intervalIntegral.integral_comp_sub_left F t
      _ = ∫ x in t - h..t, F x := by simp only [sub_zero]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    simp only [F, Set.indicator_of_mem htS]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    exact one_smul _ _
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (t - s)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (volume.measurePreserving_sub_left t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeBackwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem backwardSteklov_eq_primitive_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeBackwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  have hadd : (∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T) +
      ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T :=
    intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
  have hsub : ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      (∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hadd)
  rw [reverseTimeBackwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

/-- A positive-length forward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeForwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Continuous (reverseTimeForwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  let P : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, f s ∂reverseTimeVolume T
  have hP : Continuous P := hf.continuous_primitive 0
  have hformula : reverseTimeForwardSteklov T h f =
      fun t => h⁻¹ • (P (t + h) - P t) := by
    funext t
    exact forwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul ((hP.comp (continuous_id.add continuous_const)).sub hP)

/-- A positive-length backward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeBackwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Continuous (reverseTimeBackwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  let P : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, f s ∂reverseTimeVolume T
  have hP : Continuous P := hf.continuous_primitive 0
  have hformula : reverseTimeBackwardSteklov T h f =
      fun t => h⁻¹ • (P t - P (t - h)) := by
    funext t
    exact backwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul (hP.sub (hP.comp (continuous_id.sub continuous_const)))

/-- A forward average is Bochner integrable on every compact ordinary interval. -/
theorem integrableOn_reverseTimeForwardSteklov_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (a b : ℝ) :
    MeasureTheory.IntegrableOn (reverseTimeForwardSteklov T h f) (Set.Icc a b) volume :=
  (continuous_reverseTimeForwardSteklov T h hh f).integrableOn_Icc

/-- A backward average is Bochner integrable on every compact ordinary interval. -/
theorem integrableOn_reverseTimeBackwardSteklov_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (a b : ℝ) :
    MeasureTheory.IntegrableOn (reverseTimeBackwardSteklov T h f) (Set.Icc a b) volume :=
  (continuous_reverseTimeBackwardSteklov T h hh f).integrableOn_Icc

/-- Forward one-sided Steklov averages converge strongly in local Bochner `L²`. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let K : Set ℝ := Icc a b
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q : ℝ → ℝ := fun s => ∫ t in K, ‖f (t + s) - f t‖ ^ 2
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    simpa only [q, K] using
      tendsto_sqNorm_integral_forward_translate_on_Icc T f ha hab hb
  have hq0 : ∀ s, 0 ≤ q s := fun s => integral_nonneg fun _ => sq_nonneg _
  have haverage := tendsto_inv_mul_setIntegral_Ioc_zero q hq hq0
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T - b :=
      (eventually_lt_nhds (sub_pos.mpr hb)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, hsmall] with h hh hhT
    have hleft : (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
        ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [forwardSteklov_sub_eq_forward_window T h a b hh hhT ha hb f t ht]
    have hright : h⁻¹ * ∫ s in Ioc 0 h,
        ∫ t in K, ‖F (s + t) - F t‖ ^ 2 = h⁻¹ * ∫ s in Ioc 0 h, q s := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
      have htsS : t + s ∈ S := by
        constructor
        · exact add_pos (lt_of_lt_of_le ha ht.1) hs.1
        · calc
            t + s ≤ b + h := add_le_add ht.2 hs.2
            _ < T := by linarith
      have hstS : s + t ∈ S := by simpa only [add_comm] using htsS
      simp only [F, Set.indicator_of_mem hstS, Set.indicator_of_mem htS, add_comm]
    calc
      (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := hleft
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 :=
        sqNorm_forward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := hright
  · exact haverage

/-- Backward one-sided Steklov averages converge strongly in local Bochner `L²`. -/
theorem tendsto_backwardSteklov_sqNorm_integral_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let K : Set ℝ := Icc a b
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q : ℝ → ℝ := fun s => ∫ t in K, ‖f (t - s) - f t‖ ^ 2
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    simpa only [q, K] using
      tendsto_sqNorm_integral_backward_translate_on_Icc T f ha hab hb
  have hq0 : ∀ s, 0 ≤ q s := fun s => integral_nonneg fun _ => sq_nonneg _
  have haverage := tendsto_inv_mul_setIntegral_Ioc_zero q hq hq0
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < a :=
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, hsmall] with h hh hhA
    have hleft : (∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2) =
        ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [backwardSteklov_sub_eq_backward_window T h a b hh hhA ha hb f t ht]
    have hright : h⁻¹ * ∫ s in Ioc 0 h,
        ∫ t in K, ‖F (t - s) - F t‖ ^ 2 = h⁻¹ * ∫ s in Ioc 0 h, q s := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
      have htsS : t - s ∈ S := by
        constructor
        · exact sub_pos.mpr (lt_of_le_of_lt hs.2 (hhA.trans_le ht.1))
        · exact (sub_lt_self t hs.1).trans (ht.2.trans_lt hb)
      simp only [F, Set.indicator_of_mem htsS, Set.indicator_of_mem htS]
    calc
      (∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2 := hleft
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 :=
        sqNorm_backward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := hright
  · exact haverage

end HypoellipticAleksandrov.Parabolic.Dirichlet
