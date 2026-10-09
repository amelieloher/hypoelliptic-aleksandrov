module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Hilbert-valued reverse-time Steklov curves

This module packages the literal one-sided Steklov averages as continuous
Hilbert-valued curves on closed time collars.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The deterministic positive Steklov step used for the Hilbert representative. -/
noncomputable def reverseTimeSteklovStep (T : ℝ) (n : ℕ) : ℝ :=
  T / ((n + 2 : ℕ) : ℝ)

/-- The deterministic Steklov step is positive for positive terminal time. -/
theorem reverseTimeSteklovStep_pos (T : ℝ) (hT : 0 < T) (n : ℕ) :
    0 < reverseTimeSteklovStep T n := by
  unfold reverseTimeSteklovStep
  positivity

/-- The deterministic Steklov steps tend to zero from the right. -/
theorem tendsto_reverseTimeSteklovStep
    (T : ℝ) (hT : 0 < T) :
    Filter.Tendsto (reverseTimeSteklovStep T) Filter.atTop
      (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [reverseTimeSteklovStep, Function.comp_def] using!
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 2)
  · filter_upwards with n
    exact reverseTimeSteklovStep_pos T hT n

/-- Forward Hilbert-valued Steklov curves on a left closed time collar. -/
noncomputable def reverseTimeForwardSteklovHilbertOnIcc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (b : ℝ) :
    ℕ → C(↥(Set.Icc 0 b), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩

/-- Backward Hilbert-valued Steklov curves on a right closed time collar. -/
noncomputable def reverseTimeBackwardSteklovHilbertOnIcc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (a : ℝ) :
    ℕ → C(↥(Set.Icc a T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  fun n =>
    ⟨fun t => valueCLM hΩ
        (reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u t),
      ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
          (reverseTimeSteklovStep_pos T hT n) u)).continuousOn.restrict⟩

private theorem normSq_sub_eq_inner_add_sub_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (r s : H) :
    ‖r‖ ^ 2 - ‖s‖ ^ 2 = inner ℝ (r + s) r - inner ℝ (r + s) s := by
  rw [inner_add_left, inner_add_left, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, real_inner_comm s r]
  ring

private theorem pivot_normSq_sub_eq_dualSub_apply_add
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (r s : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ r‖ ^ 2 - ‖valueCLM hΩ s‖ ^ 2 =
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ r) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ s)) (r + s) := by
  let vr : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ r
  let vs : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ s
  have hvalue : valueCLM hΩ (r + s) = vr + vs :=
    (valueCLM hΩ).map_add r s
  change ‖vr‖ ^ 2 - ‖vs‖ ^ 2 = _
  rw [ContinuousLinearMap.sub_apply,
    scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, hvalue]
  exact normSq_sub_eq_inner_add_sub_inner vr vs

private theorem tendsto_clm_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V}
    {a : V →L[ℝ] ℝ} {b : V}
    (hf : Filter.Tendsto f L (𝓝 a)) (hg : Filter.Tendsto g L (𝓝 b)) :
    Filter.Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
  simpa only [Function.comp_def] using
    (isBoundedBilinearMap_apply.continuous.tendsto (a, b)).comp (hf.prodMk_nhds hg)

private theorem hasDerivAt_of_pivoted_curve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : ℝ → V} {U : ℝ → V →L[ℝ] ℝ} {E : ℝ → ℝ}
    {y : ℝ → V →L[ℝ] ℝ} (hx : Continuous x) {t : ℝ}
    (hpivot : ∀ r s : ℝ, E r - E s = (U r - U s) (x r + x s))
    (hderiv : HasDerivAt U (y t) t) :
    HasDerivAt E (2 * y t (x t)) t := by
  have hSlopeU : Filter.Tendsto (slope U t) (𝓝[≠] t) (𝓝 (y t)) := by
    exact hderiv.tendsto_slope
  have hxWithin : Filter.Tendsto x (𝓝[≠] t) (𝓝 (x t)) :=
    (hx.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hsum : Filter.Tendsto (fun s => x s + x t) (𝓝[≠] t) (𝓝 (x t + x t)) :=
    hxWithin.add tendsto_const_nhds
  have hEval : Filter.Tendsto
      (fun s => slope U t s (x s + x t)) (𝓝[≠] t) (𝓝 (y t (x t + x t))) :=
    tendsto_clm_apply hSlopeU hsum
  have hSlopeEq : slope E t =ᶠ[𝓝[≠] t]
      fun s => slope U t s (x s + x t) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s ≠ t := hs
    rw [slope_def_field, slope_def_module, hpivot s t,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [smul_eq_mul, sub_apply]
    field_simp [sub_ne_zero.mpr hst]
  have hSlopeE : Filter.Tendsto (slope E t) (𝓝[≠] t) (𝓝 (2 * y t (x t))) := by
    have htwice : y t (x t + x t) = 2 * y t (x t) := by
      rw [ContinuousLinearMap.map_add]
      ring
    rw [← htwice]
    exact hEval.congr' hSlopeEq.symm
  exact hasDerivAt_iff_tendsto_slope.mpr hSlopeE

private theorem mixed_energy_identity_of_pivot
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x : ℝ → H10HilbertGraph hΩ) (y : ℝ → H10HilbertGraphDual hΩ)
    (U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ)
    {a b : ℝ} (hab : a ≤ b) (hx : Continuous x) (hy : Continuous y)
    (hpivot : ∀ r s : ℝ,
      ‖valueCLM hΩ (x r)‖ ^ 2 - ‖valueCLM hΩ (x s)‖ ^ 2 =
        (U r - U s) (x r + x s))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt U (y t) t) :
    ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 =
      2 * ∫ t in Icc a b, y t (x t) := by
  let E : ℝ → ℝ := fun t => ‖valueCLM hΩ (x t)‖ ^ 2
  have hE : Continuous E := ((valueCLM hΩ).continuous.comp hx).norm.pow 2
  have hpair : Continuous (fun t => y t (x t)) := hy.clm_apply hx
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E (2 * y t (x t)) t := by
    intro t ht
    exact hasDerivAt_of_pivoted_curve hx hpivot (hderiv t ht)
  have hFTC : (∫ t in a..b, 2 * y t (x t)) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      ((continuous_const.mul hpair).intervalIntegrable a b)
  calc
    ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 = E b - E a := rfl
    _ = ∫ t in a..b, 2 * y t (x t) := hFTC.symm
    _ = 2 * ∫ t in Ioc a b, y t (x t) := by
      rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    _ = 2 * ∫ t in Icc a b, y t (x t) := by
      rw [integral_Icc_eq_integral_Ioc]

private theorem hasDerivAt_forward_mixed_gelfand
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h k t : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hth : t + h < T) (htk : t + k < T) (ht0 : 0 < t) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u s)))
      (reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t) t := by
  exact (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv
    (h := h) (t := t) hh ht0 hth).sub
    (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv
      (h := k) (t := t) hk ht0 htk)

private theorem hasDerivAt_backward_mixed_gelfand
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h k t : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hth : 0 < t - h) (htk : 0 < t - k) (htT : t < T) :
    HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u s)))
      (reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t) t := by
  exact (hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv
    (h := h) (t := t) hh hth htT).sub
    (hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv
      (h := k) (t := t) hk htk htT)

private theorem forward_mixed_pivot
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (T h k : ℝ) (u : ReverseTimeL2V hΩ T) (r s : ℝ) :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u r -
        reverseTimeForwardSteklov T k u r)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s -
        reverseTimeForwardSteklov T k u s)‖ ^ 2 =
      ((scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u r)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u r))) -
        (scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeForwardSteklov T k u s))))
        ((reverseTimeForwardSteklov T h u r - reverseTimeForwardSteklov T k u r) +
          (reverseTimeForwardSteklov T h u s - reverseTimeForwardSteklov T k u s)) := by
  simpa only [ContinuousLinearMap.map_sub] using
    pivot_normSq_sub_eq_dualSub_apply_add hΩ
      (reverseTimeForwardSteklov T h u r - reverseTimeForwardSteklov T k u r)
      (reverseTimeForwardSteklov T h u s - reverseTimeForwardSteklov T k u s)

private theorem backward_mixed_pivot
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (T h k : ℝ) (u : ReverseTimeL2V hΩ T) (r s : ℝ) :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u r -
        reverseTimeBackwardSteklov T k u r)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u s -
        reverseTimeBackwardSteklov T k u s)‖ ^ 2 =
      ((scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u r)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u r))) -
        (scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T h u s)) -
        scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ (reverseTimeBackwardSteklov T k u s))))
        ((reverseTimeBackwardSteklov T h u r - reverseTimeBackwardSteklov T k u r) +
          (reverseTimeBackwardSteklov T h u s - reverseTimeBackwardSteklov T k u s)) := by
  simpa only [ContinuousLinearMap.map_sub] using
    pivot_normSq_sub_eq_dualSub_apply_add hΩ
      (reverseTimeBackwardSteklov T h u r - reverseTimeBackwardSteklov T k u r)
      (reverseTimeBackwardSteklov T h u s - reverseTimeBackwardSteklov T k u s)

private theorem memLp_two_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

private theorem exists_sqNorm_le_average_on_Icc
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Icc a b, ‖f r‖ ^ 2 ≤
      ⨍ t, ‖f t‖ ^ 2 ∂(volume.restrict (Icc a b)) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hvol : 0 < μ.real univ := by
    dsimp only [μ]
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Icc_of_le hab.le]
    linarith
  have hμ : μ ≠ 0 := by
    intro hzero
    have hzero' : μ.real univ = 0 := by simp [hzero]
    linarith
  have hq : Integrable (fun t => ‖f t‖ ^ 2) μ := by
    exact (hf.norm.pow 2).integrableOn_Icc
  have hN : μ (Icc a b)ᶜ = 0 := by
    dsimp only [μ]
    rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
    simp
  obtain ⟨r, hr, hrq⟩ := MeasureTheory.exists_notMem_null_le_average hμ hq hN
  refine ⟨r, ?_, hrq⟩
  simpa only [mem_compl_iff, not_not] using hr

private theorem memLp_two_on_full_Icc
    {E : Type*} [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    MemLp (f : ℝ → E) (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) := by
  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    restrict_Ioo_eq_restrict_Icc] using Lp.memLp f

private theorem sqNorm_integral_eq_norm_sq_toLp
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

private theorem sqrt_sqNorm_integral_triangle
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (x y : ℝ → E)
    (hx : MemLp x (2 : ℝ≥0∞) μ) (hy : MemLp y (2 : ℝ≥0∞) μ) :
    √(∫ t, ‖x t‖ ^ 2 ∂μ) ≤
      √(∫ t, ‖x t - y t‖ ^ 2 ∂μ) + √(∫ t, ‖y t‖ ^ 2 ∂μ) := by
  let hxy := hx.sub hy
  have hEq : hx.toLp x = hxy.toLp (x - y) + hy.toLp y := by
    apply Lp.ext
    filter_upwards [hx.coeFn_toLp, hxy.coeFn_toLp, hy.coeFn_toLp,
      Lp.coeFn_add (hxy.toLp (x - y)) (hy.toLp y)] with t h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]
    simp only [Pi.sub_apply]
    abel
  have hxySq : ∫ t, ‖x t - y t‖ ^ 2 ∂μ = ‖hxy.toLp (x - y)‖ ^ 2 := by
    simpa only [Pi.sub_apply] using
      sqNorm_integral_eq_norm_sq_toLp (x - y) hxy
  rw [sqNorm_integral_eq_norm_sq_toLp x hx, hxySq,
    sqNorm_integral_eq_norm_sq_toLp y hy, hEq]
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_add_le (hxy.toLp (x - y)) (hy.toLp y)

private theorem forward_mixed_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h k a b : ℝ} (hh : 0 < h) (hk : 0 < k) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbh : b + h ≤ T) (hbk : b + k ≤ T) :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b -
        reverseTimeForwardSteklov T k u b)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a -
        reverseTimeForwardSteklov T k u a)‖ ^ 2 =
      2 * ∫ t in Icc a b,
        (reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t)
          (reverseTimeForwardSteklov T h u t - reverseTimeForwardSteklov T k u t) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t =>
    reverseTimeForwardSteklov T h u t - reverseTimeForwardSteklov T k u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t =>
    reverseTimeForwardSteklov T h g t - reverseTimeForwardSteklov T k g t
  let U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ := fun t =>
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeForwardSteklov T h u t)) -
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeForwardSteklov T k u t))
  have hx : Continuous x :=
    (continuous_reverseTimeForwardSteklov T h hh u).sub
      (continuous_reverseTimeForwardSteklov T k hk u)
  have hy : Continuous y :=
    ((continuous_reverseTimeForwardSteklov T h hh g).sub
      (continuous_reverseTimeForwardSteklov T k hk g))
  apply mixed_energy_identity_of_pivot hΩ x y U hab hx hy
    (forward_mixed_pivot hΩ T h k u)
  intro t ht
  have hderivU : HasDerivAt U (y t) t := by
    exact hasDerivAt_forward_mixed_gelfand hΩ T hT u g hderiv hh hk
      (by linarith [hbh, ht.2]) (by linarith [hbk, ht.2])
      (by linarith [ha0, ht.1])
  exact hderivU

private theorem backward_mixed_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h k a b : ℝ} (hh : 0 < h) (hk : 0 < k) (hah : 0 ≤ a - h)
    (hak : 0 ≤ a - k) (hab : a ≤ b) (hbT : b ≤ T) :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u b -
        reverseTimeBackwardSteklov T k u b)‖ ^ 2 -
      ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u a -
        reverseTimeBackwardSteklov T k u a)‖ ^ 2 =
      2 * ∫ t in Icc a b,
        (reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t)
          (reverseTimeBackwardSteklov T h u t - reverseTimeBackwardSteklov T k u t) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t =>
    reverseTimeBackwardSteklov T h u t - reverseTimeBackwardSteklov T k u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t =>
    reverseTimeBackwardSteklov T h g t - reverseTimeBackwardSteklov T k g t
  let U : ℝ → H10HilbertGraph hΩ →L[ℝ] ℝ := fun t =>
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeBackwardSteklov T h u t)) -
    scalarLpToH10HilbertGraphDual hΩ
      (valueCLM hΩ (reverseTimeBackwardSteklov T k u t))
  have hx : Continuous x :=
    (continuous_reverseTimeBackwardSteklov T h hh u).sub
      (continuous_reverseTimeBackwardSteklov T k hk u)
  have hy : Continuous y :=
    ((continuous_reverseTimeBackwardSteklov T h hh g).sub
      (continuous_reverseTimeBackwardSteklov T k hk g))
  apply mixed_energy_identity_of_pivot hΩ x y U hab hx hy
    (backward_mixed_pivot hΩ T h k u)
  intro t ht
  have hderivU : HasDerivAt U (y t) t := by
    exact hasDerivAt_backward_mixed_gelfand hΩ T hT u g hderiv hh hk
      (by linarith [hah, ht.1]) (by linarith [hak, ht.1])
      (by linarith [hbT, ht.2])
  exact hderivU

private theorem sqNorm_sub_le_two_mul_sqNorm_sub_add
    {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
  have htriangle : ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by
        congr 1
        abel
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ = ‖x - z‖ + ‖y - z‖ := by rw [norm_sub_rev z y]
  calc
    ‖x - y‖ ^ 2 ≤ (‖x - z‖ + ‖y - z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖y - z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x - z‖ - ‖y - z‖)]

private theorem add_three_le_add_three
    {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) :
    a + c + e ≤ b + d + f := by
  linarith

private theorem eventually_pairwise_sqNorm_integral_lt
    {E : Type*} [NormedAddCommGroup E]
    (T : ℝ) (F : ℕ → ℝ → E) (f : ℝ → E)
    (hF : ∀ n, MemLp (F n) (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)))
    (hlim : Filter.Tendsto
      (fun n => ∫ t in Icc 0 T, ‖F n t - f t‖ ^ 2) Filter.atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T, ‖F m t - F n t‖ ^ 2 < δ := by
  have htail : ∀ᶠ n : ℕ in Filter.atTop,
      ∫ t in Icc 0 T, ‖F n t - f t‖ ^ 2 < δ / 4 :=
    hlim.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 htail)
  refine ⟨N, fun m hm n hn => ?_⟩
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hmf : MemLp (F m - f) (2 : ℝ≥0∞) μ := (hF m).sub hf
  have hnf : MemLp (F n - f) (2 : ℝ≥0∞) μ := (hF n).sub hf
  have hmn : MemLp (F m - F n) (2 : ℝ≥0∞) μ := (hF m).sub (hF n)
  have hmfInt : Integrable (fun t => ‖F m t - f t‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using hmf.integrable_norm_pow (by norm_num)
  have hnfInt : Integrable (fun t => ‖F n t - f t‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using hnf.integrable_norm_pow (by norm_num)
  have hmnInt : Integrable (fun t => ‖F m t - F n t‖ ^ 2) μ := by
    simpa only [Pi.sub_apply] using hmn.integrable_norm_pow (by norm_num)
  have hbound : (∫ t, ‖F m t - F n t‖ ^ 2 ∂μ) ≤
      ∫ t, (2 : ℝ) * ‖F m t - f t‖ ^ 2 + 2 * ‖F n t - f t‖ ^ 2 ∂μ := by
    apply integral_mono hmnInt
      ((hmfInt.const_mul 2).add (hnfInt.const_mul 2))
    intro t
    exact sqNorm_sub_le_two_mul_sqNorm_sub_add (F m t) (F n t) (f t)
  have hm := hN m hm
  have hn := hN n hn
  have hmf2 : Integrable (fun t => (2 : ℝ) * ‖F m t - f t‖ ^ 2) μ :=
    hmfInt.const_mul 2
  have hnf2 : Integrable (fun t => (2 : ℝ) * ‖F n t - f t‖ ^ 2) μ :=
    hnfInt.const_mul 2
  change (∫ t, ‖F m t - F n t‖ ^ 2 ∂μ) < δ
  calc
    (∫ t, ‖F m t - F n t‖ ^ 2 ∂μ) ≤
        ∫ t, (2 : ℝ) * ‖F m t - f t‖ ^ 2 + 2 * ‖F n t - f t‖ ^ 2 ∂μ := hbound
    _ = 2 * (∫ t, ‖F m t - f t‖ ^ 2 ∂μ) +
        2 * (∫ t, ‖F n t - f t‖ ^ 2 ∂μ) := by
      rw [integral_add hmf2 hnf2, integral_const_mul, integral_const_mul]
    _ < δ := by linarith

private theorem sqNorm_valueCLM_sub_le_opNorm_sq_mul
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ (x - y)‖ ^ 2 ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 := by
  have h := (valueCLM hΩ).le_opNorm (x - y)
  calc
    ‖valueCLM hΩ (x - y)‖ ^ 2 ≤
        (‖valueCLM hΩ‖ * ‖x - y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 := by rw [mul_pow]

private theorem tendsto_forward_step_sqNorm_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun n => ∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f t - f t‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  exact (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f).comp
    (tendsto_reverseTimeSteklovStep T hT)

private theorem tendsto_backward_step_sqNorm_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun n => ∫ t in Icc 0 T,
        ‖reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f t - f t‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  exact (tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f).comp
    (tendsto_reverseTimeSteklovStep T hT)

private theorem eventually_forward_pairwise_sqNorm_integral_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) f t -
          reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f t‖ ^ 2 < δ := by
  apply eventually_pairwise_sqNorm_integral_lt T
    (fun n => reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) f) f
  · intro n
    exact memLp_two_on_Icc_of_continuous _
      (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) f) 0 T
  · exact memLp_two_on_full_Icc T f
  · exact tendsto_forward_step_sqNorm_error T hT f
  · exact hδ

private theorem eventually_backward_pairwise_sqNorm_integral_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ t in Icc 0 T,
        ‖reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) f t -
          reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f t‖ ^ 2 < δ := by
  apply eventually_pairwise_sqNorm_integral_lt T
    (fun n => reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) f) f
  · intro n
    exact memLp_two_on_Icc_of_continuous _
      (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) f) 0 T
  · exact memLp_two_on_full_Icc T f
  · exact tendsto_backward_step_sqNorm_error T hT f
  · exact hδ

private theorem abs_setIntegral_pairing_le_sqrt_full
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (x : ℝ → H10HilbertGraph hΩ) (y : ℝ → H10HilbertGraphDual hΩ)
    (hx : Continuous x) (hy : Continuous y)
    {a b : ℝ} (hsub : Icc a b ⊆ Icc 0 T) :
    |∫ t in Icc a b, y t (x t)| ≤
      √(∫ t in Icc 0 T, ‖y t‖ ^ 2) * √(∫ t in Icc 0 T, ‖x t‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  have hxμ : MemLp x (2 : ℝ≥0∞) μ := memLp_two_on_Icc_of_continuous x hx a b
  have hyμ : MemLp y (2 : ℝ≥0∞) μ := memLp_two_on_Icc_of_continuous y hy a b
  have hxν : MemLp x (2 : ℝ≥0∞) ν := memLp_two_on_Icc_of_continuous x hx 0 T
  have hyν : MemLp y (2 : ℝ≥0∞) ν := memLp_two_on_Icc_of_continuous y hy 0 T
  have hmul : Integrable (fun t => ‖y t‖ * ‖x t‖) μ :=
    hyμ.norm.integrable_mul hxμ.norm
  have hpair : |∫ t, y t (x t) ∂μ| ≤ ∫ t, ‖y t‖ * ‖x t‖ ∂μ := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hmul
    filter_upwards with t
    simpa only [Real.norm_eq_abs] using (y t).le_opNorm (x t)
  have hholder := integral_mul_norm_le_sqrt_mul_sqrt y x hyμ hxμ
  have hySq : ∫ t, ‖y t‖ ^ 2 ∂μ ≤ ∫ t, ‖y t‖ ^ 2 ∂ν := by
    apply setIntegral_mono_set (hyν.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _)
    exact hsub.eventuallyLE
  have hxSq : ∫ t, ‖x t‖ ^ 2 ∂μ ≤ ∫ t, ‖x t‖ ^ 2 ∂ν := by
    apply setIntegral_mono_set (hxν.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ => sq_nonneg _)
    exact hsub.eventuallyLE
  calc
    |∫ t in Icc a b, y t (x t)| = |∫ t, y t (x t) ∂μ| := rfl
    _ ≤ ∫ t, ‖y t‖ * ‖x t‖ ∂μ := hpair
    _ ≤ √(∫ t, ‖y t‖ ^ 2 ∂μ) * √(∫ t, ‖x t‖ ^ 2 ∂μ) := hholder
    _ ≤ √(∫ t, ‖y t‖ ^ 2 ∂ν) * √(∫ t, ‖x t‖ ^ 2 ∂ν) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hySq) (Real.sqrt_le_sqrt hxSq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := rfl

private theorem sqNorm_at_le_anchor_add_pairwise_integrals
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (x : ℝ → H10HilbertGraph hΩ) (y : ℝ → H10HilbertGraphDual hΩ)
    (hx : Continuous x) (hy : Continuous y)
    (K : Set ℝ) (hK : K ⊆ Icc 0 T)
    (henergy : ∀ {a b : ℝ}, a ≤ b → a ∈ K → b ∈ K →
      ‖valueCLM hΩ (x b)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 =
        2 * ∫ s in Icc a b, y s (x s))
    {r t : ℝ} (hr : r ∈ K) (ht : t ∈ K) :
    ‖valueCLM hΩ (x t)‖ ^ 2 ≤ ‖valueCLM hΩ (x r)‖ ^ 2 +
      (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := by
  let Y : ℝ := ∫ s in Icc 0 T, ‖y s‖ ^ 2
  let X : ℝ := ∫ s in Icc 0 T, ‖x s‖ ^ 2
  have hY0 : 0 ≤ Y := integral_nonneg fun _ => sq_nonneg _
  have hX0 : 0 ≤ X := integral_nonneg fun _ => sq_nonneg _
  have hcross : 2 * (√Y * √X) ≤ Y + X := by
    have h := two_mul_le_add_sq (√Y) (√X)
    simpa only [mul_assoc, Real.sq_sqrt hY0, Real.sq_sqrt hX0] using h
  rcases le_total r t with hrt | htr
  · have hsubset : Icc r t ⊆ Icc 0 T := by
      intro s hs
      exact ⟨(hK hr).1.trans hs.1, hs.2.trans (hK ht).2⟩
    have hpair := abs_setIntegral_pairing_le_sqrt_full hΩ T x y hx hy hsubset
    have henergy' := henergy hrt hr ht
    have hdiff : ‖valueCLM hΩ (x t)‖ ^ 2 - ‖valueCLM hΩ (x r)‖ ^ 2 ≤ Y + X := by
      rw [henergy']
      calc
        2 * ∫ s in Icc r t, y s (x s) ≤ 2 * |∫ s in Icc r t, y s (x s)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two
        _ ≤ 2 * (√Y * √X) := mul_le_mul_of_nonneg_left hpair zero_le_two
        _ ≤ Y + X := hcross
    linarith
  · have hsubset : Icc t r ⊆ Icc 0 T := by
      intro s hs
      exact ⟨(hK ht).1.trans hs.1, hs.2.trans (hK hr).2⟩
    have hpair := abs_setIntegral_pairing_le_sqrt_full hΩ T x y hx hy hsubset
    have henergy' := henergy htr ht hr
    have habs : |‖valueCLM hΩ (x r)‖ ^ 2 - ‖valueCLM hΩ (x t)‖ ^ 2| ≤ Y + X := by
      rw [henergy']
      calc
        |2 * ∫ s in Icc t r, y s (x s)| = 2 * |∫ s in Icc t r, y s (x s)| := by
          rw [abs_mul, abs_of_nonneg zero_le_two]
        _ ≤ 2 * (√Y * √X) := mul_le_mul_of_nonneg_left hpair zero_le_two
        _ ≤ Y + X := hcross
    have hneg : -(Y + X) ≤
        ‖valueCLM hΩ (x r)‖ ^ 2 - ‖valueCLM hΩ (x t)‖ ^ 2 :=
      neg_le_of_abs_le habs
    linarith

private theorem exists_anchor_sqNorm_valueCLM_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x)
    {a b v : ℝ} (hab : a < b) (hvol : volume.real (Icc a b) = v)
    (hsub : Icc a b ⊆ Icc 0 T) :
    ∃ r ∈ Icc a b,
      ‖valueCLM hΩ (x r)‖ ^ 2 ≤
        v⁻¹ * ‖valueCLM hΩ‖ ^ 2 * ∫ t in Icc 0 T, ‖x t‖ ^ 2 := by
  obtain ⟨r, hr, hravg⟩ := exists_sqNorm_le_average_on_Icc
    (fun t => valueCLM hΩ (x t)) ((valueCLM hΩ).continuous.comp hx) hab
  have hravg' : ‖valueCLM hΩ (x r)‖ ^ 2 ≤
      v⁻¹ * ∫ t in Icc a b, ‖valueCLM hΩ (x t)‖ ^ 2 := by
    rw [MeasureTheory.average_eq,
      MeasureTheory.measureReal_restrict_apply_univ, hvol, smul_eq_mul] at hravg
    exact hravg
  have hxA : MemLp x (2 : ℝ≥0∞) (volume.restrict (Icc a b)) :=
    memLp_two_on_Icc_of_continuous x hx a b
  have hxK : MemLp x (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) :=
    memLp_two_on_Icc_of_continuous x hx 0 T
  have hleft : Integrable (fun t => ‖valueCLM hΩ (x t)‖ ^ 2)
      (volume.restrict (Icc a b)) :=
    (((valueCLM hΩ).continuous.comp hx).norm.pow 2).integrableOn_Icc
  have hright : Integrable (fun t => ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2)
      (volume.restrict (Icc a b)) := by
    exact (hxA.integrable_norm_pow (by norm_num)).const_mul _
  have hmap : (∫ t in Icc a b, ‖valueCLM hΩ (x t)‖ ^ 2) ≤
      ∫ t in Icc a b, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2 := by
    apply integral_mono hleft hright
    intro t
    simpa only [map_zero, sub_zero] using
      sqNorm_valueCLM_sub_le_opNorm_sq_mul hΩ (x t) 0
  have hrestrict : (∫ t in Icc a b, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2) ≤
      ∫ t in Icc 0 T, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2 := by
    apply setIntegral_mono_set
      ((hxK.integrable_norm_pow (by norm_num)).const_mul _)
      (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact hsub.eventuallyLE
  refine ⟨r, hr, ?_⟩
  calc
    ‖valueCLM hΩ (x r)‖ ^ 2 ≤
        v⁻¹ * ∫ t in Icc a b, ‖valueCLM hΩ (x t)‖ ^ 2 := hravg'
    _ ≤ v⁻¹ * (∫ t in Icc a b, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hmap (inv_nonneg.mpr (by
        rw [← hvol, Real.volume_real_Icc_of_le hab.le]
        exact sub_nonneg.mpr hab.le))
    _ ≤ v⁻¹ * (∫ t in Icc 0 T, ‖valueCLM hΩ‖ ^ 2 * ‖x t‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hrestrict (inv_nonneg.mpr (by
        rw [← hvol, Real.volume_real_Icc_of_le hab.le]
        exact sub_nonneg.mpr hab.le))
    _ = v⁻¹ * ‖valueCLM hΩ‖ ^ 2 * ∫ t in Icc 0 T, ‖x t‖ ^ 2 := by
      rw [integral_const_mul]
      ring

/-- The deterministic forward Steklov curves are Cauchy uniformly in spatial `L²` on every
left closed collar `Icc 0 b` with `0 < b < T`. -/
theorem cauchySeq_reverseTimeForwardSteklovHilbertOnIcc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {b : ℝ} (hb0 : 0 < b) (hbT : b < T) :
    CauchySeq (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let c : ℝ := (b / 3)⁻¹ * ‖valueCLM hΩ‖ ^ 2
  let η : ℝ := ε ^ 2 / (c + 3)
  have hc0 : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _)
  have hc3 : 0 < c + 3 := by linarith
  have hη : 0 < η := by
    exact div_pos (sq_pos_of_pos hε) hc3
  obtain ⟨Nu, hNu⟩ := eventually_forward_pairwise_sqNorm_integral_lt T hT u hη
  obtain ⟨Ng, hNg⟩ := eventually_forward_pairwise_sqNorm_integral_lt T hT g hη
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < T - b :=
    (eventually_lt_nhds (sub_pos.mpr hbT)).filter_mono nhdsWithin_le_nhds
  have htail : ∀ᶠ n : ℕ in Filter.atTop,
      reverseTimeSteklovStep T n < T - b :=
    (tendsto_reverseTimeSteklovStep T hT).eventually hsmall
  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 htail
  refine ⟨max (max Nu Ng) Nh, ?_⟩
  intro m hm n hn
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  let x : ℝ → H10HilbertGraph hΩ := fun s =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) u s -
      reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u s
  let y : ℝ → H10HilbertGraphDual hΩ := fun s =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T m) g s -
      reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) g s
  have hmNu : m ≥ Nu := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
  have hnNu : n ≥ Nu := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hmNg : m ≥ Ng := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
  have hnNg : n ≥ Ng := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hmNh : m ≥ Nh := le_trans (le_max_right _ _) hm
  have hnNh : n ≥ Nh := le_trans (le_max_right _ _) hn
  have hU : ∫ s in Icc 0 T, ‖x s‖ ^ 2 < η := by
    simpa only [x] using hNu m hmNu n hnNu
  have hG : ∫ s in Icc 0 T, ‖y s‖ ^ 2 < η := by
    simpa only [y] using hNg m hmNg n hnNg
  have hmstep : reverseTimeSteklovStep T m < T - b := hNh m hmNh
  have hnstep : reverseTimeSteklovStep T n < T - b := hNh n hnNh
  have hx : Continuous x := by
    exact (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) u).sub
      (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) u)
  have hy : Continuous y := by
    exact (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) g).sub
      (continuous_reverseTimeForwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) g)
  have hApos : b / 3 < 2 * b / 3 := by linarith
  have hAvol : volume.real (Icc (b / 3) (2 * b / 3)) = b / 3 := by
    rw [Real.volume_real_Icc_of_le hApos.le]
    ring
  have hAsub : Icc (b / 3) (2 * b / 3) ⊆ Icc 0 T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, hbT]
  obtain ⟨r, hr, hrbound⟩ := exists_anchor_sqNorm_valueCLM_le hΩ T x hx hApos hAvol hAsub
  have hrK : r ∈ Icc 0 b := by
    constructor <;> linarith [hr.1, hr.2]
  have htK : (t : ℝ) ∈ Icc 0 b := t.2
  have hKsub : Icc 0 b ⊆ Icc 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hbT.le⟩
  have henergy : ∀ {a q : ℝ}, a ≤ q → a ∈ Icc 0 b → q ∈ Icc 0 b →
      ‖valueCLM hΩ (x q)‖ ^ 2 - ‖valueCLM hΩ (x a)‖ ^ 2 =
        2 * ∫ s in Icc a q, y s (x s) := by
    intro a q haq ha hq
    simpa only [x, y] using forward_mixed_energy_identity hΩ T hT u g hderiv
      (reverseTimeSteklovStep_pos T hT m) (reverseTimeSteklovStep_pos T hT n)
      ha.1 haq (by linarith [hq.2, hmstep]) (by linarith [hq.2, hnstep])
  have hprop := sqNorm_at_le_anchor_add_pairwise_integrals hΩ T x y hx hy
    (Icc 0 b) hKsub henergy hrK htK
  have hanchor : ‖valueCLM hΩ (x r)‖ ^ 2 ≤ c *
      (∫ s in Icc 0 T, ‖x s‖ ^ 2) := by
    simpa only [c] using hrbound
  have hsq : ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 < ε ^ 2 := by
    have hcu : c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) ≤ c * η :=
      mul_le_mul_of_nonneg_left hU.le hc0
    have hfinal : c * η + η + η < ε ^ 2 := by
      have heq : (c + 3) * η = ε ^ 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hc3]
      have hlt : c * η + η + η < (c + 3) * η := by
        calc
          c * η + η + η = (c + 2) * η := by ring
          _ < (c + 3) * η := mul_lt_mul_of_pos_right (by linarith) hη
      exact hlt.trans_eq heq
    calc
      ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 ≤
          ‖valueCLM hΩ (x r)‖ ^ 2 +
            (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := hprop
      _ ≤ c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) +
            η + η := add_three_le_add_three hanchor hG.le hU.le
      _ ≤ c * η + η + η := add_three_le_add_three hcu le_rfl le_rfl
      _ < ε ^ 2 := hfinal
  have hnorm : ‖valueCLM hΩ (x (t : ℝ))‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
  simpa only [reverseTimeForwardSteklovHilbertOnIcc, ContinuousMap.coe_mk,
    ContinuousMap.coe_mk, dist_eq_norm, ContinuousLinearMap.map_sub, x] using! hnorm

/-- The deterministic backward Steklov curves are Cauchy uniformly in spatial `L²` on every
right closed collar `Icc a T` with `0 < a < T`. -/
theorem cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {a : ℝ} (ha0 : 0 < a) (haT : a < T) :
    CauchySeq (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let c : ℝ := ((T - a) / 3)⁻¹ * ‖valueCLM hΩ‖ ^ 2
  let η : ℝ := ε ^ 2 / (c + 3)
  have hlength : 0 < (T - a) / 3 := by linarith
  have hc0 : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr hlength.le) (sq_nonneg _)
  have hc3 : 0 < c + 3 := by linarith
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) hc3
  obtain ⟨Nu, hNu⟩ := eventually_backward_pairwise_sqNorm_integral_lt T hT u hη
  obtain ⟨Ng, hNg⟩ := eventually_backward_pairwise_sqNorm_integral_lt T hT g hη
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < a :=
    (eventually_lt_nhds ha0).filter_mono nhdsWithin_le_nhds
  have htail : ∀ᶠ n : ℕ in Filter.atTop, reverseTimeSteklovStep T n < a :=
    (tendsto_reverseTimeSteklovStep T hT).eventually hsmall
  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 htail
  refine ⟨max (max Nu Ng) Nh, ?_⟩
  intro m hm n hn
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  let x : ℝ → H10HilbertGraph hΩ := fun s =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) u s -
      reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u s
  let y : ℝ → H10HilbertGraphDual hΩ := fun s =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m) g s -
      reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) g s
  have hmNu : m ≥ Nu := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
  have hnNu : n ≥ Nu := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hmNg : m ≥ Ng := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
  have hnNg : n ≥ Ng := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hmNh : m ≥ Nh := le_trans (le_max_right _ _) hm
  have hnNh : n ≥ Nh := le_trans (le_max_right _ _) hn
  have hU : ∫ s in Icc 0 T, ‖x s‖ ^ 2 < η := by
    simpa only [x] using hNu m hmNu n hnNu
  have hG : ∫ s in Icc 0 T, ‖y s‖ ^ 2 < η := by
    simpa only [y] using hNg m hmNg n hnNg
  have hmstep : reverseTimeSteklovStep T m < a := hNh m hmNh
  have hnstep : reverseTimeSteklovStep T n < a := hNh n hnNh
  have hx : Continuous x := by
    exact (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) u).sub
      (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) u)
  have hy : Continuous y := by
    exact (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T m)
      (reverseTimeSteklovStep_pos T hT m) g).sub
      (continuous_reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n)
        (reverseTimeSteklovStep_pos T hT n) g)
  have hApos : (2 * a + T) / 3 < (a + 2 * T) / 3 := by linarith
  have hAvol : volume.real (Icc ((2 * a + T) / 3) ((a + 2 * T) / 3)) = (T - a) / 3 := by
    rw [Real.volume_real_Icc_of_le hApos.le]
    ring
  have hAsub : Icc ((2 * a + T) / 3) ((a + 2 * T) / 3) ⊆ Icc 0 T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, ha0, haT]
  obtain ⟨r, hr, hrbound⟩ := exists_anchor_sqNorm_valueCLM_le hΩ T x hx hApos hAvol hAsub
  have hrK : r ∈ Icc a T := by constructor <;> linarith [hr.1, hr.2, haT]
  have htK : (t : ℝ) ∈ Icc a T := t.2
  have hKsub : Icc a T ⊆ Icc 0 T := by
    intro s hs
    exact ⟨ha0.le.trans hs.1, hs.2⟩
  have henergy : ∀ {p q : ℝ}, p ≤ q → p ∈ Icc a T → q ∈ Icc a T →
      ‖valueCLM hΩ (x q)‖ ^ 2 - ‖valueCLM hΩ (x p)‖ ^ 2 =
        2 * ∫ s in Icc p q, y s (x s) := by
    intro p q hpq hp hq
    simpa only [x, y] using backward_mixed_energy_identity hΩ T hT u g hderiv
      (reverseTimeSteklovStep_pos T hT m) (reverseTimeSteklovStep_pos T hT n)
      (by linarith [hp.1, hmstep]) (by linarith [hp.1, hnstep]) hpq hq.2
  have hprop := sqNorm_at_le_anchor_add_pairwise_integrals hΩ T x y hx hy
    (Icc a T) hKsub henergy hrK htK
  have hanchor : ‖valueCLM hΩ (x r)‖ ^ 2 ≤ c *
      (∫ s in Icc 0 T, ‖x s‖ ^ 2) := by
    simpa only [c] using hrbound
  have hsq : ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 < ε ^ 2 := by
    have hcu : c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) ≤ c * η :=
      mul_le_mul_of_nonneg_left hU.le hc0
    have hfinal : c * η + η + η < ε ^ 2 := by
      have heq : (c + 3) * η = ε ^ 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hc3]
      have hlt : c * η + η + η < (c + 3) * η := by
        calc
          c * η + η + η = (c + 2) * η := by ring
          _ < (c + 3) * η := mul_lt_mul_of_pos_right (by linarith) hη
      exact hlt.trans_eq heq
    calc
      ‖valueCLM hΩ (x (t : ℝ))‖ ^ 2 ≤
          ‖valueCLM hΩ (x r)‖ ^ 2 +
            (∫ s in Icc 0 T, ‖y s‖ ^ 2) + ∫ s in Icc 0 T, ‖x s‖ ^ 2 := hprop
      _ ≤ c * (∫ s in Icc 0 T, ‖x s‖ ^ 2) +
            η + η := add_three_le_add_three hanchor hG.le hU.le
      _ ≤ c * η + η + η := add_three_le_add_three hcu le_rfl le_rfl
      _ < ε ^ 2 := hfinal
  have hnorm : ‖valueCLM hΩ (x (t : ℝ))‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
  simpa only [reverseTimeBackwardSteklovHilbertOnIcc, ContinuousMap.coe_mk,
    ContinuousMap.coe_mk, dist_eq_norm, ContinuousLinearMap.map_sub, x] using! hnorm

end HypoellipticAleksandrov.Parabolic.Dirichlet
