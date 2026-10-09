module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weighted time energy for spacetime mollification

This module develops the kernel-derivative facts used to prove the weighted
time-energy limit for the fixed spacetime mollifier.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped Convolution ENNReal NNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy

private theorem timeDerivative_spacetimeMollifier
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) z =
      (((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(volume : Measure (TimeVelocity d))) *
          ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹) * ε⁻¹ *
        fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
          (ε⁻¹ • z) (1, 0) := by
  let c : ℝ := ((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
      ∂(volume : Measure (TimeVelocity d))) *
      ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹
  let s : TimeVelocity d → TimeVelocity d := fun y => ε⁻¹ • y
  have hu : DifferentiableAt ℝ
      (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ) (s z) :=
    (ExistsContDiffBumpBase.u_smooth (TimeVelocity d)).differentiable
      (by simp) (s z)
  have hs : HasFDerivAt s (ε⁻¹ • ContinuousLinearMap.id ℝ (TimeVelocity d)) z := by
    simpa [s, Pi.smul_def, id_eq] using (hasFDerivAt_id (𝕜 := ℝ) z).const_smul ε⁻¹
  have hcomp := fderiv_comp z hu hs.differentiableAt
  have hinner :
      fderiv ℝ (fun y : TimeVelocity d => ExistsContDiffBumpBase.u (ε⁻¹ • y)) z =
        (fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
          (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (TimeVelocity d)) := by
    change fderiv ℝ (ExistsContDiffBumpBase.u ∘ s) z = _
    rw [hcomp, hs.fderiv]
  unfold timeDerivative spacetimeMollifier
  rw [abs_of_nonneg hε.le, fderiv_const_mul]
  · rw [hinner]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring_nf
  · exact hu.comp z hs.differentiableAt

private theorem timeDerivative_spacetimeMollifier_neg
    {d : ℕ} (ε : ℝ) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) (-z) =
      -timeDerivative (spacetimeMollifier ε) z := by
  let ρ : TimeVelocity d → ℝ := spacetimeMollifier ε
  let n : TimeVelocity d → TimeVelocity d := fun y => -y
  have hρ : Differentiable ℝ ρ :=
    (spacetimeMollifier_contDiff ε).differentiable (by simp)
  have hn (y : TimeVelocity d) :
      HasFDerivAt n (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) y := by
    simpa [n, Pi.neg_def, id_eq] using (hasFDerivAt_id (𝕜 := ℝ) y).neg
  have heq : ρ ∘ n = ρ := by
    funext y
    exact spacetimeMollifier_neg ε y
  have hcomp := fderiv_comp z (hρ (-z)) (hn z).differentiableAt
  have hfderiv :
      fderiv ℝ ρ (-z) ∘L (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) =
        fderiv ℝ ρ z := by
    rw [← (hn z).fderiv, ← hcomp, heq]
  unfold timeDerivative
  change fderiv ℝ ρ (-z) (1, 0) = -fderiv ℝ ρ z (1, 0)
  have happ := congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L (1, 0)) hfderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at happ
  linarith

private theorem integrable_timeDerivative_spacetimeMollifier
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Integrable (timeDerivative (spacetimeMollifier (d := d) ε))
      (volume : Measure (TimeVelocity d)) := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (timeDerivative (spacetimeMollifier (d := d) ε)) := by
    unfold timeDerivative
    exact ((spacetimeMollifier_contDiff (d := d) ε).fderiv_right
      (by simp)).clm_apply contDiff_const
  have hsupp : HasCompactSupport
      (timeDerivative (spacetimeMollifier (d := d) ε)) := by
    unfold timeDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ)
      (spacetimeMollifier_hasCompactSupport hε) (1, 0)
  exact hsmooth.continuous.integrable_of_hasCompactSupport hsupp

private theorem bump_volume_integral_pos (d : ℕ) :
    0 < ∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
      ∂(volume : Measure (TimeVelocity d)) := by
  refine (integral_pos_iff_support_of_nonneg ExistsContDiffBumpBase.u_nonneg ?_).mpr ?_
  · exact (ExistsContDiffBumpBase.u_smooth (TimeVelocity d)).continuous
      |>.integrable_of_hasCompactSupport
        (ExistsContDiffBumpBase.u_compact_support (TimeVelocity d))
  · rw [ExistsContDiffBumpBase.u_support]
    exact Metric.measure_ball_pos (volume : Measure (TimeVelocity d)) 0 zero_lt_one

private theorem integral_norm_mul_abs_timeDerivative_spacetimeMollifier
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (∫ z : TimeVelocity d,
        ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
        ∂(volume : Measure (TimeVelocity d))) =
      (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(volume : Measure (TimeVelocity d)))⁻¹ *
        ∫ y : TimeVelocity d, ‖y‖ *
          |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
            y (1, 0)| ∂(volume : Measure (TimeVelocity d)) := by
  let A : ℝ := ∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
    ∂(volume : Measure (TimeVelocity d))
  let g : TimeVelocity d → ℝ := fun y =>
    ‖y‖ * |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ) y (1, 0)|
  have hA : A ≠ 0 := (bump_volume_integral_pos d).ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hpoint (z : TimeVelocity d) :
      ‖z‖ * |timeDerivative (spacetimeMollifier ε) z| =
        ((A * ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹ * ε⁻¹ * ε) *
          g (ε⁻¹ • z) := by
    rw [timeDerivative_spacetimeMollifier hε]
    simp only [A, g, abs_mul, abs_inv, abs_pow, abs_of_pos hε,
      abs_of_pos (bump_volume_integral_pos d),
      norm_smul, Real.norm_eq_abs]
    field_simp
  simp_rw [hpoint, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (TimeVelocity d)) g hε.le]
  change ((A * ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹ * ε⁻¹ * ε) *
      (ε ^ Module.finrank ℝ (TimeVelocity d) * ∫ y, g y ∂volume) =
    A⁻¹ * ∫ y, g y ∂volume
  field_simp

private theorem exists_uniform_firstMoment_timeDerivative_spacetimeMollifier
    (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      (∫ z : TimeVelocity d,
          ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
          ∂(volume : Measure (TimeVelocity d))) ≤ C := by
  let C : ℝ :=
    (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
        ∂(volume : Measure (TimeVelocity d)))⁻¹ *
      ∫ y : TimeVelocity d, ‖y‖ *
        |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
          y (1, 0)| ∂(volume : Measure (TimeVelocity d))
  refine ⟨C, mul_nonneg (inv_nonneg.mpr (bump_volume_integral_pos d).le)
    (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)), ?_⟩
  intro ε hε
  exact (integral_norm_mul_abs_timeDerivative_spacetimeMollifier hε).le

private theorem mul_memLp_two_of_contDiff_hasCompactSupport
    {d : ℕ} (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    MemLp (fun z => w z * q z) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  have hw : MemLp w ∞ (volume : Measure (TimeVelocity d)) :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  simpa only [mul_comm] using hq.fun_mul hw

private theorem timeDerivative_spacetimeMollification_mul
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (z : TimeVelocity d) :
    timeDerivative
        (spacetimeMollification ε (fun y => w y * q y)) z =
      ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x *
          (w (z - x) * q (z - x))
        ∂(volume : Measure (TimeVelocity d)) := by
  let f : TimeVelocity d → ℝ := fun y => w y * q y
  have hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    mul_memLp_two_of_contDiff_hasCompactSupport q w hq hwSmooth hwCompact
  have hfLoc : LocallyIntegrable f
      (volume : Measure (TimeVelocity d)) := hf.locallyIntegrable (by norm_num)
  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((spacetimeMollifier_contDiff ε).of_le (by simp)) hfLoc z
  have hkernel : HasCompactSupport
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) :=
    (spacetimeMollifier_hasCompactSupport hε).fderiv ℝ
  have hkernelCont : Continuous
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) :=
    (spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)
  have hconv : MeasureTheory.ConvolutionExistsAt
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) f z
      (ContinuousLinearMap.precompL (TimeVelocity d)
        (ContinuousLinearMap.lsmul ℝ ℝ))
      (volume : Measure (TimeVelocity d)) :=
    hkernel.convolutionExists_left _ hkernelCont hfLoc z
  have hint : Integrable
      (fun x : TimeVelocity d =>
        ((ContinuousLinearMap.precompL (TimeVelocity d)
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x)))
      (volume : Measure (TimeVelocity d)) := by
    exact hconv
  unfold timeDerivative spacetimeMollification
  rw [hderiv.fderiv]
  calc
    ((fderiv ℝ (spacetimeMollifier ε) ⋆[ContinuousLinearMap.precompL
        (TimeVelocity d) (ContinuousLinearMap.lsmul ℝ ℝ), volume] f) z) (1, 0) =
        ∫ x : TimeVelocity d,
          (((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x))) (1, 0)
          ∂volume := by
      change (∫ x : TimeVelocity d,
          ((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x)) ∂volume) (1, 0) = _
      exact ((ContinuousLinearMap.apply ℝ ℝ (1, 0)).integral_comp_comm hint).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp [f]

private theorem integrable_kernel_mul_memLp_two_mul_translate
    {d : ℕ} (k f g : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        k p.1 * f p.2 * g (p.2 - p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hfirst : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        |k p.1| * f p.2 ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    hk.abs.mul_prod hf.integrable_sq
  have hbase : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        |k p.1| * g p.2 ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    hk.abs.mul_prod hg.integrable_sq
  have hsecond : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        |k p.1| * g (p.2 - p.1) ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    simpa only [Function.comp_def] using
      (measurePreserving_prod_sub
        (volume : Measure (TimeVelocity d))
        (volume : Measure (TimeVelocity d))).integrable_comp_of_integrable hbase
  apply (hfirst.add hsecond).mono'
  · exact hk.1.comp_fst |>.mul hf.aestronglyMeasurable.comp_snd |>.mul <| by
      simpa only [Function.comp_def] using hg.aestronglyMeasurable.comp_snd.comp_measurePreserving
        (measurePreserving_prod_sub
          (volume : Measure (TimeVelocity d))
          (volume : Measure (TimeVelocity d)))
  · exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hk0 := abs_nonneg (k p.1)
      have hs := sq_nonneg (|f p.2| - |g (p.2 - p.1)|)
      have hfabs : |f p.2| ^ 2 = f p.2 ^ 2 := sq_abs (f p.2)
      have hgabs : |g (p.2 - p.1)| ^ 2 = g (p.2 - p.1) ^ 2 :=
        sq_abs (g (p.2 - p.1))
      simp only [Pi.add_apply]
      nlinarith

private theorem integrable_pairing_doubleIntegrand
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        q p.2 * timeDerivative (spacetimeMollifier ε) p.1 *
          (w (p.2 - p.1) * q (p.2 - p.1)))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hwq := mul_memLp_two_of_contDiff_hasCompactSupport q w hq hwSmooth hwCompact
  have h := integrable_kernel_mul_memLp_two_mul_translate
    (timeDerivative (spacetimeMollifier ε)) q (fun z => w z * q z)
    (integrable_timeDerivative_spacetimeMollifier hε) hq hwq
  apply h.congr
  exact ae_of_all _ fun p => by ring_nf

private theorem pairing_eq_integral_integral
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d))) =
      ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        q y * timeDerivative (spacetimeMollifier ε) x *
          (w (y - x) * q (y - x))
        ∂(volume : Measure (TimeVelocity d))
      ∂(volume : Measure (TimeVelocity d)) := by
  have hdouble := integrable_pairing_doubleIntegrand hε q w hq hwSmooth hwCompact
  calc
    _ = ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        q z * timeDerivative (spacetimeMollifier ε) x *
          (w (z - x) * q (z - x)) ∂volume ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only
        rw [timeDerivative_spacetimeMollification_mul hε q w hq hwSmooth hwCompact]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring_nf
    _ = _ := by
      apply integral_integral_swap
      convert hdouble.swap using 1
      funext p
      rcases p with ⟨x, y⟩
      rfl

private theorem pairing_eq_translated_integral_integral
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d))) =
      ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w y * q y * q (y + x)
        ∂(volume : Measure (TimeVelocity d))
      ∂(volume : Measure (TimeVelocity d)) := by
  rw [pairing_eq_integral_integral hε q w hq hwSmooth hwCompact]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hmp : MeasurePreserving (MeasurableEquiv.addLeft x)
        (volume : Measure (TimeVelocity d)) volume :=
      measurePreserving_add_left (volume : Measure (TimeVelocity d)) x
    have htranslate := hmp.integral_comp'
      (fun y : TimeVelocity d =>
        q y * timeDerivative (spacetimeMollifier ε) x *
          (w (y - x) * q (y - x)))
    dsimp only
    rw [← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      simp only [MeasurableEquiv.coe_addLeft, add_sub_cancel_left]
      ring_nf

private theorem pairing_eq_neg_reflected_integral_integral
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d))) =
      -(∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w (y + x) * q y * q (y + x)
        ∂(volume : Measure (TimeVelocity d))
      ∂(volume : Measure (TimeVelocity d))) := by
  rw [pairing_eq_integral_integral hε q w hq hwSmooth hwCompact]
  have hmp : MeasurePreserving (MeasurableEquiv.neg (TimeVelocity d))
      (volume : Measure (TimeVelocity d)) volume :=
    Measure.measurePreserving_neg (volume : Measure (TimeVelocity d))
  have hreflect := hmp.integral_comp'
    (fun x : TimeVelocity d => ∫ y : TimeVelocity d,
      q y * timeDerivative (spacetimeMollifier ε) x *
        (w (y - x) * q (y - x)) ∂volume)
  rw [← hreflect, ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ y : TimeVelocity d,
      q y * timeDerivative (spacetimeMollifier ε) (-x) *
        (w (y - (-x)) * q (y - (-x))) ∂volume) = _
    dsimp only
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      rw [timeDerivative_spacetimeMollifier_neg]
      simp only [sub_neg_eq_add]
      ring_nf

private theorem pairing_eq_half_symmetrized
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d))) =
      (1 / 2 : ℝ) * ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          q y * q (y + x)
        ∂(volume : Measure (TimeVelocity d))
      ∂(volume : Measure (TimeVelocity d)) := by
  let P : ℝ := ∫ z : TimeVelocity d,
    q z * timeDerivative
      (spacetimeMollification ε (fun y => w y * q y)) z ∂volume
  let A : ℝ := ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * w y * q y * q (y + x) ∂volume ∂volume
  let B : ℝ := ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * w (y + x) * q y * q (y + x)
      ∂volume ∂volume
  have hPA : P = A :=
    pairing_eq_translated_integral_integral hε q w hq hwSmooth hwCompact
  have hPB : P = -B :=
    pairing_eq_neg_reflected_integral_integral hε q w hq hwSmooth hwCompact
  have hdouble := integrable_pairing_doubleIntegrand hε q w hq hwSmooth hwCompact
  have hAprod : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        timeDerivative (spacetimeMollifier ε) p.1 * w p.2 * q p.2 * q (p.2 + p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    have hc := (measurePreserving_prod_add
      (volume : Measure (TimeVelocity d))
      (volume : Measure (TimeVelocity d))).integrable_comp_of_integrable hdouble
    apply hc.congr
    exact ae_of_all _ fun p => by
      simp only [Function.comp_apply, add_sub_cancel_left, add_comm]
      ring_nf
  have hnegProd : MeasurePreserving
      (fun p : TimeVelocity d × TimeVelocity d => (-p.1, p.2))
      ((volume : Measure (TimeVelocity d)).prod volume)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure (TimeVelocity d))).prod
      (MeasurePreserving.id (volume : Measure (TimeVelocity d)))
  have hBprod : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        timeDerivative (spacetimeMollifier ε) p.1 * w (p.2 + p.1) *
          q p.2 * q (p.2 + p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    have hc := hnegProd.integrable_comp_of_integrable hdouble
    apply hc.neg.congr
    exact ae_of_all _ fun p => by
      change -(q p.2 * timeDerivative (spacetimeMollifier ε) (-p.1) *
        (w (p.2 - (-p.1)) * q (p.2 - (-p.1)))) = _
      rw [timeDerivative_spacetimeMollifier_neg]
      simp only [sub_neg_eq_add]
      ring_nf
  have hAB : (∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
      timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
        q y * q (y + x) ∂volume ∂volume) = A - B := by
    have hAouter : Integrable (fun x : TimeVelocity d => ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w y * q y * q (y + x) ∂volume)
        (volume : Measure (TimeVelocity d)) := by
      simpa only [Prod.fst, Prod.snd] using hAprod.integral_prod_left
    have hBouter : Integrable (fun x : TimeVelocity d => ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w (y + x) * q y * q (y + x) ∂volume)
        (volume : Measure (TimeVelocity d)) := by
      simpa only [Prod.fst, Prod.snd] using hBprod.integral_prod_left
    simp only [A, B]
    rw [← integral_sub hAouter hBouter]
    apply integral_congr_ae
    filter_upwards [hAprod.prod_right_ae, hBprod.prod_right_ae] with x hAi hBi
    rw [← integral_sub hAi hBi]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by ring_nf
  change P = _
  rw [hAB]
  linarith

private theorem memLp_add_translate
    {d : ℕ} (x : TimeVelocity d) (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    MemLp (fun y => f (y + x)) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  simpa only [Function.comp_def, add_comm] using
    hf.comp_measurePreserving
      (measurePreserving_add_left (volume : Measure (TimeVelocity d)) x)

private theorem integral_abs_mul_add_translate_le
    {d : ℕ} (x : TimeVelocity d) (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    (∫ y : TimeVelocity d, |f y| * |g (y + x)|
      ∂(volume : Measure (TimeVelocity d))) ≤
      Real.sqrt (∫ y : TimeVelocity d, f y ^ 2 ∂volume) *
        Real.sqrt (∫ y : TimeVelocity d, g y ^ 2 ∂volume) := by
  have hgt := memLp_add_translate x g hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure (TimeVelocity d)))
    (f := fun y => |f y|) (g := fun y => |g (y + x)|)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ fun _ => abs_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs, abs_abs] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs, abs_abs] using hgt.norm)
  have htranslate : (∫ y : TimeVelocity d, g (y + x) ^ 2 ∂volume) =
      ∫ y : TimeVelocity d, g y ^ 2 ∂volume := by
    have hmp : MeasurePreserving (MeasurableEquiv.addLeft x)
        (volume : Measure (TimeVelocity d)) volume :=
      measurePreserving_add_left (volume : Measure (TimeVelocity d)) x
    simpa only [MeasurableEquiv.coe_addLeft, add_comm] using
      hmp.integral_comp' (fun y : TimeVelocity d => g y ^ 2)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two, sq_abs, htranslate] using hholder

private theorem exists_lipschitzWith_weight
    {d : ℕ} (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    ∃ K : ℝ≥0, LipschitzWith K w := by
  exact ContDiff.lipschitzWith_of_hasCompactSupport hwCompact hwSmooth (by simp)

private theorem abs_integral_symmetrized_inner_le
    {d : ℕ} (K : ℝ≥0) (w : TimeVelocity d → ℝ)
    (hwLip : LipschitzWith K w)
    (x : TimeVelocity d) (k : ℝ)
    (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    |∫ y : TimeVelocity d,
        k * (w y - w (y + x)) * f y * g (y + x)
        ∂(volume : Measure (TimeVelocity d))| ≤
      |k| * (K : ℝ) * ‖x‖ *
        (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2 ∂volume) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2 ∂volume)) := by
  have hfg : Integrable (fun y : TimeVelocity d => |f y| * |g (y + x)|)
      (volume : Measure (TimeVelocity d)) := by
    have hgt := memLp_add_translate x g hg
    simpa only [Pi.mul_def, Real.norm_eq_abs, abs_abs] using hf.norm.integrable_mul hgt.norm
  calc
    _ = ‖∫ y : TimeVelocity d,
        k * (w y - w (y + x)) * f y * g (y + x) ∂volume‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ y : TimeVelocity d,
        ‖k * (w y - w (y + x)) * f y * g (y + x)‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : TimeVelocity d,
        (|k| * (K : ℝ) * ‖x‖) * (|f y| * |g (y + x)|) ∂volume := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun _ => norm_nonneg _
      · exact hfg.const_mul (|k| * (K : ℝ) * ‖x‖)
      · exact ae_of_all _ fun y => by
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
          have hw : |w y - w (y + x)| ≤ (K : ℝ) * ‖x‖ := by
            simpa [Real.norm_eq_abs] using hwLip.norm_sub_le y (y + x)
          calc
            _ = (|k| * |w y - w (y + x)|) *
                (|f y| * |g (y + x)|) := by ring
            _ ≤ (|k| * ((K : ℝ) * ‖x‖)) *
                (|f y| * |g (y + x)|) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hw (abs_nonneg k))
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = _ := by ring
    _ = (|k| * (K : ℝ) * ‖x‖) *
        ∫ y : TimeVelocity d, |f y| * |g (y + x)| ∂volume := by
      rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_abs_mul_add_translate_le x f g hf hg)
      (mul_nonneg (mul_nonneg (abs_nonneg _) K.coe_nonneg) (norm_nonneg _))

private theorem integrable_norm_mul_abs_timeDerivative_spacetimeMollifier
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : TimeVelocity d =>
      ‖x‖ * |timeDerivative (spacetimeMollifier ε) x|)
      (volume : Measure (TimeVelocity d)) := by
  have hdtCont : Continuous
      (timeDerivative (spacetimeMollifier (d := d) ε)) := by
    unfold timeDerivative
    exact ((spacetimeMollifier_contDiff (d := d) ε).continuous_fderiv
      (by simp)).clm_apply continuous_const
  have hdtCompact : HasCompactSupport
      (timeDerivative (spacetimeMollifier (d := d) ε)) := by
    unfold timeDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ)
      (spacetimeMollifier_hasCompactSupport hε) (1, 0)
  exact (continuous_norm.mul hdtCont.abs).integrable_of_hasCompactSupport
    hdtCompact.abs.mul_left

private theorem abs_symmetrized_bilinear_le
    {d : ℕ} {ε M : ℝ} (hε : 0 < ε)
    (hmoment : (∫ x : TimeVelocity d,
      ‖x‖ * |timeDerivative (spacetimeMollifier ε) x| ∂volume) ≤ M)
    (K : ℝ≥0) (w : TimeVelocity d → ℝ) (hwLip : LipschitzWith K w)
    (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    |∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x) ∂volume ∂volume| ≤
      (K : ℝ) * M *
        (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2 ∂volume) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2 ∂volume)) := by
  let S : ℝ := Real.sqrt (∫ y : TimeVelocity d, f y ^ 2 ∂volume) *
    Real.sqrt (∫ y : TimeVelocity d, g y ^ 2 ∂volume)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hweighted :=
    integrable_norm_mul_abs_timeDerivative_spacetimeMollifier (d := d) hε
  change _ ≤ (K : ℝ) * M * S
  calc
    _ = ‖∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x) ∂volume ∂volume‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : TimeVelocity d, |∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x) ∂volume| ∂volume := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x : TimeVelocity d => ∫ y : TimeVelocity d,
          timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
            f y * g (y + x) ∂volume)
    _ ≤ ∫ x : TimeVelocity d,
        ((K : ℝ) * S) *
          (‖x‖ * |timeDerivative (spacetimeMollifier ε) x|) ∂volume := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun _ => abs_nonneg _
      · exact hweighted.const_mul ((K : ℝ) * S)
      · exact ae_of_all _ fun x => by
          have hx := abs_integral_symmetrized_inner_le K w hwLip x
            (timeDerivative (spacetimeMollifier ε) x) f g hf hg
          change _ ≤ ((K : ℝ) * S) *
            (‖x‖ * |timeDerivative (spacetimeMollifier ε) x|)
          change _ ≤ _ at hx
          nlinarith [K.coe_nonneg, norm_nonneg x,
            abs_nonneg (timeDerivative (spacetimeMollifier ε) x)]
    _ = ((K : ℝ) * S) * ∫ x : TimeVelocity d,
        ‖x‖ * |timeDerivative (spacetimeMollifier ε) x| ∂volume := by
      rw [integral_const_mul]
    _ ≤ ((K : ℝ) * S) * M :=
      mul_le_mul_of_nonneg_left hmoment (mul_nonneg K.coe_nonneg hS)
    _ = _ := by ring

private theorem exists_uniform_symmetrized_bilinear_bound
    {d : ℕ} (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ (f g : TimeVelocity d → ℝ),
      MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) →
      MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) →
      |∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
          timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
            f y * g (y + x) ∂volume ∂volume| ≤
        C * (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2 ∂volume) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2 ∂volume)) := by
  obtain ⟨K, hwLip⟩ := exists_lipschitzWith_weight w hwSmooth hwCompact
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_firstMoment_timeDerivative_spacetimeMollifier d
  refine ⟨(K : ℝ) * M, mul_nonneg K.coe_nonneg hM, ?_⟩
  intro ε hε f g hf hg
  exact abs_symmetrized_bilinear_le hε (hmoment hε) K w hwLip f g hf hg

private def symmetrizedBilinear
    {d : ℕ} (ε : ℝ) (w f g : TimeVelocity d → ℝ) : ℝ :=
  ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
      f y * g (y + x) ∂volume ∂volume

private theorem integrable_symmetrizedBilinear_double
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w f g : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * (w p.2 - w (p.2 + p.1)) *
        f p.2 * g (p.2 + p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hwf := mul_memLp_two_of_contDiff_hasCompactSupport f w hf hwSmooth hwCompact
  have hwg := mul_memLp_two_of_contDiff_hasCompactSupport g w hg hwSmooth hwCompact
  have hk := integrable_timeDerivative_spacetimeMollifier (d := d) hε
  have hbaseA := integrable_kernel_mul_memLp_two_mul_translate
    (timeDerivative (spacetimeMollifier ε)) g (fun y => w y * f y) hk hg hwf
  have hAcomp := (measurePreserving_prod_add
    (volume : Measure (TimeVelocity d))
    (volume : Measure (TimeVelocity d))).integrable_comp_of_integrable hbaseA
  have hA : Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * w p.2 * f p.2 * g (p.2 + p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    apply hAcomp.congr
    exact ae_of_all _ fun p => by
      simp only [Function.comp_apply, add_sub_cancel_left, add_comm]
      ring
  have hbaseB := integrable_kernel_mul_memLp_two_mul_translate
    (fun x => timeDerivative (spacetimeMollifier ε) (-x)) f
      (fun y => w y * g y)
      ((integrable_timeDerivative_spacetimeMollifier hε).comp_neg) hf hwg
  have hnegProd : MeasurePreserving
      (fun p : TimeVelocity d × TimeVelocity d => (-p.1, p.2))
      ((volume : Measure (TimeVelocity d)).prod volume)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure (TimeVelocity d))).prod
      (MeasurePreserving.id (volume : Measure (TimeVelocity d)))
  have hBcomp := hnegProd.integrable_comp_of_integrable hbaseB
  have hB : Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * w (p.2 + p.1) *
        f p.2 * g (p.2 + p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    apply hBcomp.congr
    exact ae_of_all _ fun p => by
      change timeDerivative (spacetimeMollifier ε) (-(-p.1)) * f p.2 *
        (w (p.2 - (-p.1)) * g (p.2 - (-p.1))) = _
      simp only [neg_neg, sub_neg_eq_add]
      ring
  apply (hA.sub hB).congr
  exact ae_of_all _ fun p => by
    simp only [Pi.sub_apply]
    ring

private theorem integrable_symmetrizedBilinear_outer
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w f g : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable (fun x : TimeVelocity d => ∫ y : TimeVelocity d,
      timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
        f y * g (y + x) ∂volume)
      (volume : Measure (TimeVelocity d)) := by
  simpa only [Prod.fst, Prod.snd] using
    (integrable_symmetrizedBilinear_double hε w f g hwSmooth hwCompact hf hg).integral_prod_left

private theorem symmetrizedBilinear_quadratic_sub
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w q p : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    symmetrizedBilinear ε w q q - symmetrizedBilinear ε w p p =
      symmetrizedBilinear ε w (q - p) q +
        symmetrizedBilinear ε w p (q - p) := by
  have hqp := hq.sub hp
  have hqq := integrable_symmetrizedBilinear_outer hε w q q hwSmooth hwCompact hq hq
  have hpp := integrable_symmetrizedBilinear_outer hε w p p hwSmooth hwCompact hp hp
  have hdq := integrable_symmetrizedBilinear_outer hε w (q - p) q
    hwSmooth hwCompact hqp hq
  have hpd := integrable_symmetrizedBilinear_outer hε w p (q - p)
    hwSmooth hwCompact hp hqp
  unfold symmetrizedBilinear
  rw [← integral_sub hqq hpp, ← integral_add hdq hpd]
  apply integral_congr_ae
  filter_upwards [
    (integrable_symmetrizedBilinear_double hε w q q hwSmooth hwCompact hq hq).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w p p hwSmooth hwCompact hp hp).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w (q - p) q hwSmooth hwCompact hqp hq).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w p (q - p) hwSmooth hwCompact hp hqp).prod_right_ae]
      with x hqqx hppx hdqx hpdx
  rw [← integral_sub hqqx hppx, ← integral_add hdqx hpdx]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [Pi.sub_apply]
    ring

private theorem exists_uniform_pairing_quadratic_continuity
    {d : ℕ} (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ (q p : TimeVelocity d → ℝ),
      MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) →
      MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) →
      |(∫ z : TimeVelocity d, q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z ∂volume) -
        ∫ z : TimeVelocity d, p z * timeDerivative
          (spacetimeMollification ε (fun y => w y * p y)) z ∂volume| ≤
        (1 / 2 : ℝ) * C *
          (Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume) *
              Real.sqrt (∫ y : TimeVelocity d, q y ^ 2 ∂volume) +
            Real.sqrt (∫ y : TimeVelocity d, p y ^ 2 ∂volume) *
              Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_symmetrized_bilinear_bound w hwSmooth hwCompact
  refine ⟨C, hC, ?_⟩
  intro ε hε q p hq hp
  have hqp := hq.sub hp
  have hqPair := pairing_eq_half_symmetrized hε q w hq hwSmooth hwCompact
  have hpPair := pairing_eq_half_symmetrized hε p w hp hwSmooth hwCompact
  have hquad := symmetrizedBilinear_quadratic_sub hε w q p
    hwSmooth hwCompact hq hp
  have hfirst := hbound hε (q - p) q hqp hq
  have hsecond := hbound hε p (q - p) hp hqp
  change |_ - _| ≤ _
  rw [hqPair, hpPair]
  change |(1 / 2 : ℝ) * symmetrizedBilinear ε w q q -
      (1 / 2 : ℝ) * symmetrizedBilinear ε w p p| ≤ _
  rw [← mul_sub, hquad, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |symmetrizedBilinear ε w (q - p) q +
        symmetrizedBilinear ε w p (q - p)| ≤
        (1 / 2 : ℝ) * (|symmetrizedBilinear ε w (q - p) q| +
          |symmetrizedBilinear ε w p (q - p)|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ _ := by
      simp only [Pi.sub_apply] at hfirst hsecond
      have hadd := add_le_add hfirst hsecond
      calc
        _ ≤ (1 / 2 : ℝ) *
            (C * (Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume) *
                Real.sqrt (∫ y : TimeVelocity d, q y ^ 2 ∂volume)) +
              C * (Real.sqrt (∫ y : TimeVelocity d, p y ^ 2 ∂volume) *
                Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume))) :=
          mul_le_mul_of_nonneg_left hadd (by norm_num)
        _ = _ := by ring

private theorem timeDerivative_mul
    {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : TimeVelocity d) :
    timeDerivative (fun y => f y * g y) z =
      timeDerivative f z * g z + f z * timeDerivative g z := by
  unfold timeDerivative
  change (fderiv ℝ (f * g) z) (1, 0) = _
  rw [fderiv_mul (hf z) (hg z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem smooth_weighted_time_energy_identity
    {d : ℕ} (p w : TimeVelocity d → ℝ)
    (hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p)
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hpt : MemLp (timeDerivative p) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
      p z * timeDerivative (fun y => w y * p y) z ∂volume) =
      (1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * p z ^ 2 ∂volume := by
  have hpDiff : Differentiable ℝ p := hpSmooth.differentiable (by simp)
  have hwDiff : Differentiable ℝ w := hwSmooth.differentiable (by simp)
  have hwpDiff : Differentiable ℝ (fun z => w z * p z) := hwDiff.mul hpDiff
  have hwTop : MemLp w ∞ (volume : Measure (TimeVelocity d)) :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  have hwtSmooth : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const
  have hwtCompact : HasCompactSupport (timeDerivative w) := by
    unfold timeDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hwCompact (1, 0)
  have hwtTop : MemLp (timeDerivative w) ∞
      (volume : Measure (TimeVelocity d)) :=
    hwtSmooth.continuous.memLp_of_hasCompactSupport hwtCompact
  have hpp : Integrable (fun z : TimeVelocity d => p z * p z) volume := by
    simpa only [Pi.mul_def] using hp.integrable_mul hp
  have hwtpp : Integrable (fun z : TimeVelocity d =>
      timeDerivative w z * p z ^ 2) volume := by
    have := hpp.mul_of_top_left hwtTop
    apply this.congr
    exact ae_of_all _ fun z => by simp only [Pi.mul_apply, pow_two]; ring
  have hppt : Integrable (fun z : TimeVelocity d => p z * timeDerivative p z) volume := by
    simpa only [Pi.mul_def] using hp.integrable_mul hpt
  have hwppt : Integrable (fun z : TimeVelocity d =>
      (w z * p z) * timeDerivative p z) volume := by
    have := hppt.mul_of_top_left hwTop
    apply this.congr
    exact ae_of_all _ fun z => by simp only [Pi.mul_apply]; ring
  have hdtwp_p : Integrable (fun z : TimeVelocity d =>
      timeDerivative (fun y => w y * p y) z * p z) volume := by
    apply (hwtpp.add hwppt).congr
    exact ae_of_all _ fun z => by
      simp only [Pi.add_apply]
      rw [timeDerivative_mul w p hwDiff hpDiff]
      ring
  have hp_dtwp : Integrable (fun z : TimeVelocity d =>
      p z * timeDerivative (fun y => w y * p y) z) volume := by
    apply hdtwp_p.congr
    exact ae_of_all _ fun z => by ring
  have hwpp : Integrable (fun z : TimeVelocity d => (w z * p z) * p z) volume := by
    have := hpp.mul_of_top_left hwTop
    apply this.congr
    exact ae_of_all _ fun z => by simp only [Pi.mul_apply]; ring
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (TimeVelocity d))) (v := (1, 0))
    hdtwp_p hwppt hwpp (fun z _ => hwpDiff z) (fun z _ => hpDiff z)
  change (∫ z, (w z * p z) * timeDerivative p z ∂volume) =
      -(∫ z, timeDerivative (fun y => w y * p y) z * p z ∂volume) at hibp
  have hsplit : (∫ z : TimeVelocity d,
      p z * timeDerivative (fun y => w y * p y) z ∂volume) =
      (∫ z : TimeVelocity d, timeDerivative w z * p z ^ 2 ∂volume) +
        ∫ z : TimeVelocity d, (w z * p z) * timeDerivative p z ∂volume := by
    rw [← integral_add hwtpp hwppt]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      rw [timeDerivative_mul w p hwDiff hpDiff]
      ring
  rw [hsplit]
  have hcomm : (∫ z : TimeVelocity d,
      timeDerivative (fun y => w y * p y) z * p z ∂volume) =
      ∫ z : TimeVelocity d,
        p z * timeDerivative (fun y => w y * p y) z ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun z => by ring
  rw [hcomm] at hibp
  linarith

private theorem timeDerivative_spacetimeMollification
    {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (z : TimeVelocity d) :
    timeDerivative (spacetimeMollification ε f) z =
      ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * f (z - x)
        ∂(volume : Measure (TimeVelocity d)) := by
  have hfLoc : LocallyIntegrable f
      (volume : Measure (TimeVelocity d)) := hf.locallyIntegrable (by norm_num)
  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((spacetimeMollifier_contDiff ε).of_le (by simp)) hfLoc z
  have hkernel : HasCompactSupport
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) :=
    (spacetimeMollifier_hasCompactSupport hε).fderiv ℝ
  have hkernelCont : Continuous
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) :=
    (spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)
  have hconv : MeasureTheory.ConvolutionExistsAt
      (fderiv ℝ (spacetimeMollifier (d := d) ε)) f z
      (ContinuousLinearMap.precompL (TimeVelocity d)
        (ContinuousLinearMap.lsmul ℝ ℝ))
      (volume : Measure (TimeVelocity d)) :=
    hkernel.convolutionExists_left _ hkernelCont hfLoc z
  have hint : Integrable
      (fun x : TimeVelocity d =>
        ((ContinuousLinearMap.precompL (TimeVelocity d)
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x)))
      (volume : Measure (TimeVelocity d)) := hconv
  unfold timeDerivative spacetimeMollification
  rw [hderiv.fderiv]
  calc
    ((fderiv ℝ (spacetimeMollifier ε) ⋆[ContinuousLinearMap.precompL
        (TimeVelocity d) (ContinuousLinearMap.lsmul ℝ ℝ), volume] f) z) (1, 0) =
        ∫ x : TimeVelocity d,
          (((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x))) (1, 0)
          ∂volume := by
      change (∫ x : TimeVelocity d,
          ((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x)) ∂volume) (1, 0) = _
      exact ((ContinuousLinearMap.apply ℝ ℝ (1, 0)).integral_comp_comm hint).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by rfl

private theorem spacetimeMollification_smooth_memLp
    {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (q : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d))) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeMollification δ q) ∧
      MemLp (spacetimeMollification δ q) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d)) := by
  exact ⟨contDiff_spacetimeMollification hδ q
      (hq.locallyIntegrable (by norm_num)),
    SpacetimeMollifierL2.spacetimeMollification_memLp hδ q hq⟩

private theorem timeDerivative_mul_memLp_two
    {d : ℕ} (p w : TimeVelocity d → ℝ)
    (hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p)
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hpt : MemLp (timeDerivative p) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    MemLp (timeDerivative (fun y => w y * p y)) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  have hpDiff : Differentiable ℝ p := hpSmooth.differentiable (by simp)
  have hwDiff : Differentiable ℝ w := hwSmooth.differentiable (by simp)
  have hwTop : MemLp w ∞ (volume : Measure (TimeVelocity d)) :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  have hwtSmooth : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const
  have hwtCompact : HasCompactSupport (timeDerivative w) := by
    unfold timeDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hwCompact (1, 0)
  have hwtTop : MemLp (timeDerivative w) ∞
      (volume : Measure (TimeVelocity d)) :=
    hwtSmooth.continuous.memLp_of_hasCompactSupport hwtCompact
  have hfirst : MemLp (fun z => timeDerivative w z * p z) (2 : ℝ≥0∞) volume :=
    by simpa only [mul_comm] using hp.fun_mul hwtTop
  have hsecond : MemLp (fun z => w z * timeDerivative p z) (2 : ℝ≥0∞) volume :=
    by simpa only [mul_comm] using hpt.fun_mul hwTop
  have heq : timeDerivative (fun y => w y * p y) = fun z =>
      timeDerivative w z * p z + w z * timeDerivative p z := by
    funext z
    rw [timeDerivative_mul w p hwDiff hpDiff]
  rw [heq]
  simpa only [Pi.add_def] using hfirst.add hsecond

private theorem tendsto_smooth_pairing
    {d : ℕ} (p w : TimeVelocity d → ℝ)
    (hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p)
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hpt : MemLp (timeDerivative p) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    Tendsto (fun ε : ℝ => ∫ z : TimeVelocity d,
      p z * timeDerivative
        (spacetimeMollification ε (fun y => w y * p y)) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d,
        p z * timeDerivative (fun y => w y * p y) z ∂volume)) := by
  let f : TimeVelocity d → ℝ := fun y => w y * p y
  let df : TimeVelocity d → ℝ := timeDerivative f
  have hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f := hwSmooth.mul hpSmooth
  have hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
    mul_memLp_two_of_contDiff_hasCompactSupport p w hp hwSmooth hwCompact
  have hdf : MemLp df (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
    timeDerivative_mul_memLp_two p w hpSmooth hp hpt hwSmooth hwCompact
  have hweak : HasWeakTimeDerivOn Set.univ f df :=
    HypoellipticAleksandrov.Parabolic.contDiffOn_one_hasWeakTimeDerivOn
      Set.univ isOpen_univ f ((hfSmooth.of_le (by norm_num)).contDiffOn)
  have hcomm : ∀ {ε : ℝ}, 0 < ε →
      timeDerivative (spacetimeMollification ε f) = spacetimeMollification ε df := by
    intro ε hε
    exact SpacetimeMollifier.timeDerivative_spacetimeMollification hε f df
      (hf.locallyIntegrable (by norm_num)) (hdf.locallyIntegrable (by norm_num)) hweak
  have ht := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    (fun ε : ℝ => p) (fun ε => spacetimeMollification ε df) p df
    (μ := (volume : Measure (TimeVelocity d)))
    (l := 𝓝[>] (0 : ℝ))
    (Eventually.of_forall fun _ => hp)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε
        exact SpacetimeMollifierL2.spacetimeMollification_memLp hε df hdf)
    hp hdf
    (by
      have hz : (fun _ : ℝ => eLpNorm
          (fun _ : TimeVelocity d => (0 : ℝ)) (2 : ℝ≥0∞) volume) =
          fun _ : ℝ => (0 : ℝ≥0∞) := by
        funext n
        exact eLpNorm_zero
      simpa only [sub_self, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0)))
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub df hdf)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hcomm hε]

private theorem tendsto_smooth_pairing_to_half
    {d : ℕ} (p w : TimeVelocity d → ℝ)
    (hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p)
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hpt : MemLp (timeDerivative p) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    Tendsto (fun ε : ℝ => ∫ z : TimeVelocity d,
      p z * timeDerivative
        (spacetimeMollification ε (fun y => w y * p y)) z ∂volume)
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * p z ^ 2 ∂volume)) := by
  rw [← smooth_weighted_time_energy_identity p w hpSmooth hp hpt hwSmooth hwCompact]
  exact tendsto_smooth_pairing p w hpSmooth hp hpt hwSmooth hwCompact

private theorem integrable_abs_kernel_mul_sq_translate
    {d : ℕ} (k f : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      |k p.2| * f (p.1 - p.2) ^ 2)
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  have hbase : Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      f p.1 ^ 2 * |k p.2|)
      ((volume : Measure (TimeVelocity d)).prod volume) :=
    hf.integrable_sq.mul_prod hk.abs
  have h := (measurePreserving_sub_prod
    (volume : Measure (TimeVelocity d))
    (volume : Measure (TimeVelocity d))).integrable_comp_of_integrable hbase
  apply h.congr
  exact ae_of_all _ fun p => by
    simp only [Function.comp_apply]
    ring

private theorem ae_sq_integral_kernel_mul_translate_le
    {d : ℕ} (k f : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    ∀ᵐ z : TimeVelocity d ∂volume,
      |∫ x : TimeVelocity d, k x * f (z - x) ∂volume| ^ 2 ≤
        (∫ x : TimeVelocity d, |k x| ∂volume) *
          ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume := by
  have hsections := (integrable_abs_kernel_mul_sq_translate k f hk hf).prod_right_ae
  filter_upwards [hsections] with z hz
  let a : TimeVelocity d → ℝ := fun x => Real.sqrt |k x|
  let b : TimeVelocity d → ℝ := fun x => Real.sqrt |k x| * |f (z - x)|
  have haSq : Integrable (fun x => a x ^ 2) volume := by
    apply hk.abs.congr
    exact ae_of_all _ fun x => by simp only [a, Real.sq_sqrt (abs_nonneg _)]
  have ha : MemLp a (2 : ℝ≥0∞) volume :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hk.1.norm)).2 haSq
  have hbSq : Integrable (fun x => b x ^ 2) volume := by
    apply hz.congr
    exact ae_of_all _ fun x => by
      simp only [b, mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]
  have hsub : AEStronglyMeasurable (fun x : TimeVelocity d => f (z - x)) volume := by
    have hmp : MeasurePreserving (fun x : TimeVelocity d => z - x) volume volume := by
      simpa only [Function.comp_def, sub_eq_add_neg] using
        (measurePreserving_add_left (volume : Measure (TimeVelocity d)) z).comp
          (Measure.measurePreserving_neg (volume : Measure (TimeVelocity d)))
    exact hf.aestronglyMeasurable.comp_measurePreserving hmp
  have hbMeas : AEStronglyMeasurable b volume :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hk.1.norm).mul hsub.norm
  have hb : MemLp b (2 : ℝ≥0∞) volume :=
    (memLp_two_iff_integrable_sq hbMeas).2 hbSq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure (TimeVelocity d))) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => Real.sqrt_nonneg _)
    (ae_of_all _ fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa using ha) (by simpa using hb)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hrewrite : (∫ x : TimeVelocity d,
      Real.sqrt |k x| * (Real.sqrt |k x| * |f (z - x)|) ∂volume) =
      ∫ x : TimeVelocity d, |k x| * |f (z - x)| ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
  rw [hrewrite] at hholder
  have haInt : (∫ x : TimeVelocity d, Real.sqrt |k x| ^ 2 ∂volume) =
      ∫ x : TimeVelocity d, |k x| ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => Real.sq_sqrt (abs_nonneg _)
  have hbInt : (∫ x : TimeVelocity d,
      Real.sqrt |k x| ^ 2 * f (z - x) ^ 2 ∂volume) =
      ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [Real.sq_sqrt (abs_nonneg _)]
  rw [haInt, hbInt] at hholder
  have habs : |∫ x : TimeVelocity d, k x * f (z - x) ∂volume| ≤
      Real.sqrt (∫ x : TimeVelocity d, |k x| ∂volume) *
        Real.sqrt (∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume) := by
    calc
      _ ≤ ∫ x : TimeVelocity d, |k x| * |f (z - x)| ∂volume := by
        calc
          _ = ‖∫ x : TimeVelocity d, k x * f (z - x) ∂volume‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ ∫ x : TimeVelocity d, ‖k x * f (z - x)‖ ∂volume :=
            norm_integral_le_integral_norm _
          _ = _ := by
            apply integral_congr_ae
            exact ae_of_all _ fun x => by
              dsimp only
              rw [Real.norm_eq_abs, abs_mul]
      _ ≤ _ := by
        simpa only [Real.sqrt_eq_rpow, one_div] using hholder
  have hleft := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    |>.2 habs
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => abs_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))] at hleft
  exact hleft

private theorem memLp_integral_kernel_mul_translate
    {d : ℕ} (k f : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    MemLp (fun z => ∫ x : TimeVelocity d, k x * f (z - x) ∂volume)
      (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) := by
  have hjoint : AEStronglyMeasurable
      (fun p : TimeVelocity d × TimeVelocity d => k p.2 * f (p.1 - p.2))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
    have hfcomp : AEStronglyMeasurable
        (fun p : TimeVelocity d × TimeVelocity d => f (p.1 - p.2))
        ((volume : Measure (TimeVelocity d)).prod volume) := by
      simpa only [Function.comp_def] using hf.aestronglyMeasurable.comp_fst.comp_measurePreserving
        (measurePreserving_sub_prod
          (volume : Measure (TimeVelocity d))
          (volume : Measure (TimeVelocity d)))
    exact hk.1.comp_snd.mul hfcomp
  have houtMeas := hjoint.integral_prod_right'
  have hright : Integrable (fun z : TimeVelocity d =>
      (∫ x : TimeVelocity d, |k x| ∂volume) *
        ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume) volume := by
    exact (integrable_abs_kernel_mul_sq_translate k f hk hf).integral_prod_left.const_mul _
  apply (memLp_two_iff_integrable_sq houtMeas).2
  apply hright.mono' (houtMeas.pow 2)
  filter_upwards [ae_sq_integral_kernel_mul_translate_le k f hk hf] with z hz
  rw [Real.norm_eq_abs, Pi.pow_apply, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using hz

private theorem integral_sq_integral_kernel_mul_translate_le
    {d : ℕ} (k f : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    (∫ z : TimeVelocity d,
      (∫ x : TimeVelocity d, k x * f (z - x) ∂volume) ^ 2 ∂volume) ≤
      (∫ x : TimeVelocity d, |k x| ∂volume) ^ 2 *
        ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
  let K : ℝ := ∫ x : TimeVelocity d, |k x| ∂volume
  have hweighted := integrable_abs_kernel_mul_sq_translate k f hk hf
  have hright : Integrable (fun z : TimeVelocity d =>
      K * ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume) volume :=
    hweighted.integral_prod_left.const_mul K
  calc
    _ ≤ ∫ z : TimeVelocity d,
        K * ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 ∂volume := by
      apply integral_mono_ae
        (memLp_integral_kernel_mul_translate k f hk hf).integrable_sq hright
      filter_upwards [ae_sq_integral_kernel_mul_translate_le k f hk hf] with z hz
      simpa only [K, sq_abs] using hz
    _ = K * ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        |k x| * f (z - x) ^ 2 ∂volume ∂volume := by
      rw [integral_const_mul]
    _ = K * ∫ x : TimeVelocity d, ∫ z : TimeVelocity d,
        |k x| * f (z - x) ^ 2 ∂volume ∂volume := by
      rw [integral_integral_swap (by
        convert hweighted using 1
        funext p
        rcases p with ⟨z, x⟩
        rfl)]
    _ = K ^ 2 * ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
      have htranslate (x : TimeVelocity d) :
          (∫ z : TimeVelocity d, f (z - x) ^ 2 ∂volume) =
            ∫ z : TimeVelocity d, f z ^ 2 ∂volume := by
        have hmp : MeasurePreserving (MeasurableEquiv.addLeft (-x)) volume volume :=
          measurePreserving_add_left (volume : Measure (TimeVelocity d)) (-x)
        simpa only [MeasurableEquiv.coe_addLeft, sub_eq_add_neg, add_comm] using
          hmp.integral_comp' (fun z : TimeVelocity d => f z ^ 2)
      simp_rw [integral_const_mul, htranslate]
      rw [integral_mul_const]
      ring
    _ = _ := rfl

private theorem timeDerivative_spacetimeMollification_memLp
    {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (q : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    MemLp (timeDerivative (spacetimeMollification δ q)) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  have hconv := memLp_integral_kernel_mul_translate
    (timeDerivative (spacetimeMollifier δ)) q
    (integrable_timeDerivative_spacetimeMollifier hδ) hq
  rw [show timeDerivative (spacetimeMollification δ q) =
      fun z => ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier δ) x * q (z - x) ∂volume by
    funext z
    exact timeDerivative_spacetimeMollification hδ q hq z]
  exact hconv

private theorem sqrt_integral_sq_eq_eLpNorm_toReal
    {d : ℕ} (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Real.sqrt (∫ z : TimeVelocity d, f z ^ 2 ∂volume) =
      (eLpNorm f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _),
    ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow,
    one_div]

private theorem tendsto_weighted_sq_integral
    {d : ℕ} (w q : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Tendsto (fun δ : ℝ => ∫ z : TimeVelocity d,
      timeDerivative w z * spacetimeMollification δ q z ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, timeDerivative w z * q z ^ 2 ∂volume)) := by
  let a : ℝ → TimeVelocity d → ℝ := fun δ => spacetimeMollification δ q
  let b : ℝ → TimeVelocity d → ℝ := fun δ z =>
    timeDerivative w z * spacetimeMollification δ q z
  let b0 : TimeVelocity d → ℝ := fun z => timeDerivative w z * q z
  have hwtSmooth : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const
  have hwtCompact : HasCompactSupport (timeDerivative w) := by
    unfold timeDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hwCompact (1, 0)
  have hwtTop : MemLp (timeDerivative w) ∞ volume :=
    hwtSmooth.continuous.memLp_of_hasCompactSupport hwtCompact
  have hb0 : MemLp b0 (2 : ℝ≥0∞) volume := by
    simpa only [b0, mul_comm] using hq.fun_mul hwtTop
  have haMem : ∀ᶠ δ : ℝ in 𝓝[>] 0, MemLp (a δ) (2 : ℝ≥0∞) volume := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hδ q hq
  have hbMem : ∀ᶠ δ : ℝ in 𝓝[>] 0, MemLp (b δ) (2 : ℝ≥0∞) volume := by
    filter_upwards [haMem] with δ hδ
    simpa only [b, mul_comm] using hδ.fun_mul hwtTop
  have haT := SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub q hq
  have hbT : Tendsto (fun δ : ℝ => eLpNorm (fun z => b δ z - b0 z)
      (2 : ℝ≥0∞) volume) (𝓝[>] 0) (𝓝 0) := by
    have huT : Tendsto (fun δ : ℝ =>
        eLpNorm (timeDerivative w) ∞ volume *
          eLpNorm (spacetimeMollification δ q - q) (2 : ℝ≥0∞) volume)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => eLpNorm (timeDerivative w) ∞ volume)
          (𝓝[>] 0) (𝓝 (eLpNorm (timeDerivative w) ∞ volume)))
        (Or.inr ENNReal.zero_ne_top) haT
        (Or.inr hwtTop.eLpNorm_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0))
      huT
    · exact Eventually.of_forall fun _ => bot_le
    · filter_upwards [haMem] with δ hδ
      have hle := eLpNorm_smul_le_mul_eLpNorm
        (p := ∞) (q := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
        hwtTop.aestronglyMeasurable (hδ.sub hq).aestronglyMeasurable
      simpa only [a, b, b0, Pi.smul_def', smul_eq_mul, Pi.sub_def,
        Pi.mul_def, mul_sub] using hle
  have ht := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    a b q b0 haMem hbMem hq hb0 haT hbT
  simpa only [a, b, b0, pow_two, mul_assoc, mul_comm, mul_left_comm] using ht

/-- Weighted time-energy limit for raw global `L²` data. -/
theorem tendsto_integral_mul_timeDerivative_spacetimeMollification_mul
    {d : ℕ} (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    Tendsto
      (fun ε : ℝ => ∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d)))
      (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * q z ^ 2
        ∂(volume : Measure (TimeVelocity d)))) := by
  let P : (TimeVelocity d → ℝ) → ℝ → ℝ := fun f ε => ∫ z : TimeVelocity d,
    f z * timeDerivative (spacetimeMollification ε (fun y => w y * f y)) z ∂volume
  let R : (TimeVelocity d → ℝ) → ℝ := fun f =>
    (1 / 2 : ℝ) * ∫ z : TimeVelocity d, timeDerivative w z * f z ^ 2 ∂volume
  obtain ⟨C, hC, hcont⟩ := exists_uniform_pairing_quadratic_continuity w hwSmooth hwCompact
  have hD : Tendsto (fun δ : ℝ =>
      (eLpNorm (spacetimeMollification δ q - q) (2 : ℝ≥0∞) volume).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
        (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub q hq)
  have hErr : Tendsto (fun δ : ℝ => C *
      (eLpNorm (spacetimeMollification δ q - q) (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm q (2 : ℝ≥0∞) volume).toReal) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hD).mul tendsto_const_nhds
  have hR : Tendsto (fun δ : ℝ => R (spacetimeMollification δ q))
      (𝓝[>] 0) (𝓝 (R q)) := by
    exact (tendsto_const_nhds.mul
      (tendsto_weighted_sq_integral w q hwSmooth hwCompact hq))
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  have heventErr := hErr.eventually (Metric.ball_mem_nhds 0 hη3)
  have heventR := hR.eventually (Metric.ball_mem_nhds (R q) hη3)
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      δ ∈ Ioi 0 ∧
      C * (eLpNorm (spacetimeMollification δ q - q) (2 : ℝ≥0∞) volume).toReal *
        (eLpNorm q (2 : ℝ≥0∞) volume).toReal ∈ Metric.ball 0 (η / 3) ∧
      R (spacetimeMollification δ q) ∈ Metric.ball (R q) (η / 3) := by
    filter_upwards [self_mem_nhdsWithin, heventErr, heventR] with δ hδ hδErr hδR
    exact ⟨hδ, hδErr, hδR⟩
  rcases hall.exists with ⟨δ, hδ, hδErr, hδR⟩
  let p : TimeVelocity d → ℝ := spacetimeMollification δ q
  have hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p :=
    (spacetimeMollification_smooth_memLp hδ q hq).1
  have hp : MemLp p (2 : ℝ≥0∞) volume :=
    (spacetimeMollification_smooth_memLp hδ q hq).2
  have hpt : MemLp (timeDerivative p) (2 : ℝ≥0∞) volume :=
    timeDerivative_spacetimeMollification_memLp hδ q hq
  have hpLimit := tendsto_smooth_pairing_to_half p w hpSmooth hp hpt hwSmooth hwCompact
  have hpClose := hpLimit.eventually (Metric.ball_mem_nhds (R p) hη3)
  filter_upwards [hpClose, self_mem_nhdsWithin] with ε hεp hε
  have hqp := hcont hε q p hq hp
  have hpNorm := SpacetimeMollifierL2.eLpNorm_spacetimeMollification_le hδ q hq
  change eLpNorm p (2 : ℝ≥0∞) volume ≤ eLpNorm q (2 : ℝ≥0∞) volume at hpNorm
  have hqpReal : Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume) =
      (eLpNorm (p - q) (2 : ℝ≥0∞) volume).toReal := by
    rw [show (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume) =
        ∫ y : TimeVelocity d, (p - q) y ^ 2 ∂volume by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by simp only [Pi.sub_apply]; ring]
    exact sqrt_integral_sq_eq_eLpNorm_toReal (p - q) (hp.sub hq)
  have hpair : |P q ε - P p ε| ≤ C *
      (eLpNorm (p - q) (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm q (2 : ℝ≥0∞) volume).toReal := by
    calc
      _ ≤ 1 / 2 * C *
          (Real.sqrt (∫ y, (q y - p y) ^ 2 ∂volume) *
              Real.sqrt (∫ y, q y ^ 2 ∂volume) +
            Real.sqrt (∫ y, p y ^ 2 ∂volume) *
              Real.sqrt (∫ y, (q y - p y) ^ 2 ∂volume)) := hqp
      _ ≤ _ := by
        rw [hqpReal, sqrt_integral_sq_eq_eLpNorm_toReal q hq,
          sqrt_integral_sq_eq_eLpNorm_toReal p hp]
        have hpReal := ENNReal.toReal_mono hq.eLpNorm_ne_top hpNorm
        have hpReal' := mul_le_mul_of_nonneg_right hpReal
          (show 0 ≤ (eLpNorm (p - q) (2 : ℝ≥0∞) volume).toReal from ENNReal.toReal_nonneg)
        have hpReal'' := mul_le_mul_of_nonneg_left hpReal' hC
        nlinarith
  have hErrLt : C * (eLpNorm (p - q) (2 : ℝ≥0∞) volume).toReal *
      (eLpNorm q (2 : ℝ≥0∞) volume).toReal < η / 3 := by
    rw [Metric.mem_ball, Real.dist_eq] at hδErr
    simpa only [p, sub_zero, abs_of_nonneg
      (mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)] using hδErr
  change dist (P q ε) (R q) < η
  rw [Real.dist_eq]
  calc
    |P q ε - R q| ≤ |P q ε - P p ε| + |P p ε - R p| + |R p - R q| := by
      rw [show P q ε - R q = (P q ε - P p ε) +
          ((P p ε - R p) + (R p - R q)) by ring]
      have h₁ := abs_add_le (P q ε - P p ε) ((P p ε - R p) + (R p - R q))
      have h₂ := abs_add_le (P p ε - R p) (R p - R q)
      linarith
    _ < η / 3 + η / 3 + η / 3 := by
      gcongr
      · exact hpair.trans_lt hErrLt
      · simpa only [Real.dist_eq] using hεp
      · simpa only [Metric.mem_ball, Real.dist_eq] using hδR
    _ = η := by ring

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
