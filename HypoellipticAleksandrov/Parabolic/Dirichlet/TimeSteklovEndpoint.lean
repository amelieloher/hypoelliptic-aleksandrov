module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov

/-!
# Endpoint-safe reverse-time Steklov convergence

This module upgrades the strict-interior Steklov convergence theorem to the
whole closed time interval.  The proof uses the zero extension only inside
ordinary Lebesgue integrals, so no endpoint values are interpreted as traces.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem endpoint_forward_window_product_memLp
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
  have hplusK : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2)) (2 : ℝ≥0∞)
      (μs.prod μt) := by
    simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
      hplus.restrict (univ ×ˢ K)
  exact hplusK.sub hzeroK

private theorem endpoint_sqNorm_integral_eq_norm_sq_toLp
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hF.coeFn_toLp,
    hF.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

private theorem endpoint_tendsto_sqNorm_integral_translate_add_on_of_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (s : Set ℝ) :
    Tendsto (fun h : ℝ => ∫ t in s, ‖F (t + h) - F t‖ ^ 2) (𝓝 0) (𝓝 0) := by
  let f : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hF.toLp F
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hcont : Continuous (fun h : ℝ => DomAddAct.mk h +ᵥ f) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have hzero : DomAddAct.mk (0 : ℝ) +ᵥ f = f := by simp
  have hcontsub : Continuous (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) :=
    hcont.sub continuous_const
  have hvalue : (DomAddAct.mk (0 : ℝ) +ᵥ f) - f = 0 := by
    rw [hzero, sub_self]
  have hsub : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0) (𝓝 0) := by
    have hat : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0)
        (𝓝 ((DomAddAct.mk (0 : ℝ) +ᵥ f) - f)) := hcontsub.continuousAt
    rw [hvalue] at hat
    exact hat
  have hnorm : Tendsto (fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa using hsub.norm.pow 2
  refine squeeze_zero (g := fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun h => ?_) hnorm
  let htrans : MemLp (fun t : ℝ => F (h + t)) (2 : ℝ≥0∞) volume :=
    hF.comp_measurePreserving (measurePreserving_add_left volume h)
  let hdiff : MemLp (fun t : ℝ => F (h + t) - F t) (2 : ℝ≥0∞) volume :=
    htrans.sub hF
  let q : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hdiff.toLp _
  let qS : Lp (α := ℝ) E (2 : ℝ≥0∞) (volume.restrict s) :=
    ((Lp.memLp q).restrict s).toLp q
  have hq : q =ᵐ[volume] fun t : ℝ => F (h + t) - F t := by
    simpa [q] using hdiff.coeFn_toLp
  have hqS : qS =ᵐ[volume.restrict s] q := by
    simpa [qS] using MemLp.coeFn_toLp ((Lp.memLp q).restrict s)
  have hsq : (∫ t in s, ‖F (t + h) - F t‖ ^ 2) = ‖qS‖ ^ 2 := by
    change (∫ t, ‖F (t + h) - F t‖ ^ 2 ∂volume.restrict s) = _
    have hqSsq := endpoint_sqNorm_integral_eq_norm_sq_toLp (qS : ℝ → E) (Lp.memLp qS)
    rw [Lp.toLp_coeFn qS (Lp.memLp qS)] at hqSsq
    rw [← hqSsq]
    apply integral_congr_ae
    filter_upwards [hqS, ae_restrict_of_ae hq] with t htS ht
    rw [htS, ht, add_comm]
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Lp_toLp_restrict_le s q) 2

private theorem endpoint_forward_window_sqNorm_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (s + t) - F t‖ ^ 2 := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    endpoint_forward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  simpa only [MeasureTheory.integral] using integral_integral_swap hPhiSq

private theorem endpoint_ae_memLp_forward_window_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (s + t) - F t) (2 : ℝ≥0∞)
        (volume.restrict (Ioc 0 h)) := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    endpoint_forward_window_product_memLp F hF h K
  have hPhiInt : Integrable (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable (by norm_num)
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  filter_upwards [hPhiInt.prod_left_ae, hPhiSq.prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem endpoint_sqNorm_smul_window_integral_le
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

private theorem endpoint_sqNorm_forward_window_average_le
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
  letI : IsFiniteMeasure μt := by exact inferInstance
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 : ℝ≥0∞)
      (μs.prod μt) := by
    simpa only [μs, μt] using endpoint_forward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.1 + z.2) - F z.2‖ ^ 2)
      (μs.prod μt) := hPhi.integrable_norm_pow (by norm_num)
  have hright : Integrable (fun t => h⁻¹ *
      ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs) μt :=
    (hPhiSq.integral_prod_right).const_mul _
  have hslice : ∀ᵐ t ∂μt,
      MemLp (fun s => F (s + t) - F t) (2 : ℝ≥0∞) μs := by
    simpa only [μs, μt] using endpoint_ae_memLp_forward_window_slice F hF h K
  have hbound : (∫ t, ‖h⁻¹ • ∫ s, F (s + t) - F t ∂μs‖ ^ 2 ∂μt) ≤
      ∫ t, h⁻¹ * ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hright
    filter_upwards [hslice] with t ht
    exact endpoint_sqNorm_smul_window_integral_le h hh _ ht
  calc
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2) =
        ∫ t, ‖h⁻¹ • ∫ s, F (s + t) - F t ∂μs‖ ^ 2 ∂μt := rfl
    _ ≤ ∫ t, h⁻¹ * ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := hbound
    _ = h⁻¹ * ∫ t, ∫ s, ‖F (s + t) - F t‖ ^ 2 ∂μs ∂μt := by
      rw [integral_const_mul]
    _ = h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 := by
      rw [← endpoint_forward_window_sqNorm_integral_swap F hF h K]

private theorem endpoint_backward_window_product_memLp
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

private theorem endpoint_backward_window_sqNorm_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (t - s) - F t‖ ^ 2 := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    endpoint_backward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  simpa only [MeasureTheory.integral] using integral_integral_swap hPhiSq

private theorem endpoint_ae_memLp_backward_window_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (t - s) - F t) (2 : ℝ≥0∞)
        (volume.restrict (Ioc 0 h)) := by
  let hPhi : MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 : ℝ≥0∞)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    endpoint_backward_window_product_memLp F hF h K
  have hPhiInt : Integrable (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable (by norm_num)
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) :=
    hPhi.integrable_norm_pow (by norm_num)
  filter_upwards [hPhiInt.prod_left_ae, hPhiSq.prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem endpoint_sqNorm_backward_window_average_le
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
    simpa only [μs, μt] using endpoint_backward_window_product_memLp F hF h K
  have hPhiSq : Integrable (fun z : ℝ × ℝ => ‖F (z.2 - z.1) - F z.2‖ ^ 2)
      (μs.prod μt) := hPhi.integrable_norm_pow (by norm_num)
  have hright : Integrable (fun t => h⁻¹ *
      ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs) μt :=
    (hPhiSq.integral_prod_right).const_mul _
  have hslice : ∀ᵐ t ∂μt,
      MemLp (fun s => F (t - s) - F t) (2 : ℝ≥0∞) μs := by
    simpa only [μs, μt] using endpoint_ae_memLp_backward_window_slice F hF h K
  have hbound : (∫ t, ‖h⁻¹ • ∫ s, F (t - s) - F t ∂μs‖ ^ 2 ∂μt) ≤
      ∫ t, h⁻¹ * ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hright
    filter_upwards [hslice] with t ht
    exact endpoint_sqNorm_smul_window_integral_le h hh _ ht
  calc
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2) =
        ∫ t, ‖h⁻¹ • ∫ s, F (t - s) - F t ∂μs‖ ^ 2 ∂μt := rfl
    _ ≤ ∫ t, h⁻¹ * ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := hbound
    _ = h⁻¹ * ∫ t, ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := by
      rw [integral_const_mul]
    _ = h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 := by
      rw [← endpoint_backward_window_sqNorm_integral_swap F hF h K]

private theorem endpoint_tendsto_inv_mul_setIntegral_Ioc_zero
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

private theorem endpoint_forward_sub_eq_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    reverseTimeForwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (s + t) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let W : Set ℝ := Ioc t (t + h)
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict measurableSet_Ioc]
    rw [← integral_indicator measurableSet_Ioc]
    have hindicator : W.indicator F = (W ∩ S).indicator f := by
      funext x
      simp only [F, Set.indicator_indicator]
    rw [hindicator]
    exact (integral_indicator (measurableSet_Ioc.inter measurableSet_Ioo)).symm
  have hshift : (∫ s in Ioc 0 h, F (s + t)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (s + t)) = ∫ s in (0 : ℝ)..h, F (s + t) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in (0 : ℝ) + t..h + t, F x :=
        intervalIntegral.integral_comp_add_right F t
      _ = ∫ x in t..t + h, F x := by simp only [zero_add, add_comm h t]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    have hFt : F t = f t := by
      change S.indicator (f : ℝ → E) t = f t
      exact Set.indicator_of_mem ht (f : ℝ → E)
    rw [hFt, one_smul]
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (s + t)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (measurePreserving_add_right volume t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeForwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem endpoint_backward_sub_eq_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    reverseTimeBackwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (t - s) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let W : Set ℝ := Ioc (t - h) t
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict measurableSet_Ioc]
    rw [← integral_indicator measurableSet_Ioc]
    have hindicator : W.indicator F = (W ∩ S).indicator f := by
      funext x
      simp only [F, Set.indicator_indicator]
    rw [hindicator]
    exact (integral_indicator (measurableSet_Ioc.inter measurableSet_Ioo)).symm
  have hshift : (∫ s in Ioc 0 h, F (t - s)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (t - s)) = ∫ s in (0 : ℝ)..h, F (t - s) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in t - h..t - 0, F x := intervalIntegral.integral_comp_sub_left F t
      _ = ∫ x in t - h..t, F x := by simp only [sub_zero]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    have hFt : F t = f t := by
      change S.indicator (f : ℝ → E) t = f t
      exact Set.indicator_of_mem ht (f : ℝ → E)
    rw [hFt, one_smul]
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (t - s)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (volume.measurePreserving_sub_left t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeBackwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem endpoint_ae_mem_Ioo_on_Icc (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with t ht
  exact ht.mpr

/-- Forward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let K : Set ℝ := Icc 0 T
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨le_rfl, hT.le⟩
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q : ℝ → ℝ := fun s => ∫ t in K, ‖F (s + t) - F t‖ ^ 2
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    simpa only [q, add_comm] using
      (endpoint_tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF K).mono_left
        nhdsWithin_le_nhds
  have hq0 : ∀ s, 0 ≤ q s := fun s => integral_nonneg fun _ => sq_nonneg _
  have haverage := endpoint_tendsto_inv_mul_setIntegral_Ioc_zero q hq hq0
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    filter_upwards [hpos] with h hh
    have hleft : (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
        ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [endpoint_ae_mem_Ioo_on_Icc T] with t ht
      rw [endpoint_forward_sub_eq_window T h hh f t ht]
    calc
      (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := hleft
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 :=
        endpoint_sqNorm_forward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := rfl
  · exact haverage

/-- Backward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  let K : Set ℝ := Icc 0 T
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨le_rfl, hT.le⟩
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q : ℝ → ℝ := fun s => ∫ t in K, ‖F (t - s) - F t‖ ^ 2
  have hplus := endpoint_tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF K
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_neg (0 : ℝ)
  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    have hlocal : Tendsto (fun h : ℝ => ∫ t in K, ‖F (t - h) - F t‖ ^ 2)
        (𝓝 0) (𝓝 0) := by
      simpa only [sub_eq_add_neg, Function.comp_def] using hplus.comp hneg
    simpa only [q] using hlocal.mono_left nhdsWithin_le_nhds
  have hq0 : ∀ s, 0 ≤ q s := fun s => integral_nonneg fun _ => sq_nonneg _
  have haverage := endpoint_tendsto_inv_mul_setIntegral_Ioc_zero q hq hq0
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    filter_upwards [hpos] with h hh
    have hleft : (∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2) =
        ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [endpoint_ae_mem_Ioo_on_Icc T] with t ht
      rw [endpoint_backward_sub_eq_window T h hh f t ht]
    calc
      (∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2 := hleft
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 :=
        endpoint_sqNorm_backward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := rfl
  · exact haverage

end HypoellipticAleksandrov.Parabolic.Dirichlet
