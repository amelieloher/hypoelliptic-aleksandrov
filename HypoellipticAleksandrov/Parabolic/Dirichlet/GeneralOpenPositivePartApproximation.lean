module

public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.H1.LevelSets
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Positive-part approximation on a general open set

This file strengthens an explicit supported smooth approximation of a
nonnegative `H¹` representative to one whose smooth approximants are
pointwise nonnegative.  The construction takes a subsequence converging
almost everywhere and applies the one-sided smooth positive-part
regularizer at a vanishing scale.

The gradient argument uses the exact level-set fact that the selected weak
gradient vanishes almost everywhere on `{u = 0}`.  Thus positivity is gained
without hiding a truncation or density theorem in an assumption.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- The `L²` dominated-convergence lemma needed below does not require the
ambient measure to be finite. -/
private theorem tendsto_eLpNorm_two_zero_of_ae_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hboundMem : MemLp bound (2 : ℝ≥0∞) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (2 : ℝ≥0∞) μ) atTop (𝓝 0) := by
  let G : ℕ → α → ℝ≥0∞ := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  let B : α → ℝ≥0∞ := fun x => ‖bound x‖ₑ ^ (2 : ℝ)
  have hGMeas : ∀ n, AEMeasurable (G n) μ := by
    intro n
    exact (hF n).enorm.pow_const _
  have hGBound : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    have henorm : ‖F n x‖ₑ ≤ ‖bound x‖ₑ := by
      simpa only [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal hx
    exact ENNReal.rpow_le_rpow henorm (by norm_num)
  have hBFinite : ∫⁻ x, B x ∂μ ≠ ∞ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hboundMem).ne
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [enorm_zero, Function.comp_def] using (continuous_enorm.tendsto 0).comp hx
    simpa only [G, Function.comp_def, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp
        henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence'
        B hGMeas hGBound hBFinite hGZero
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _)]
  simpa only [G, Function.comp_def, ENNReal.toReal_ofNat,
      one_div, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp hint

private theorem fderiv_smoothPositivePartApprox_comp_basisVec
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {δ : ℝ} (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => smoothPositivePartApprox 0 δ (φ y)) x) (basisVec i) =
      smoothPositivePartStep 0 δ (φ x) *
        (fderiv ℝ φ x) (basisVec i) := by
  simpa only [deriv_smoothPositivePartApprox] using
    fderiv_comp_basisVec
      ((smoothPositivePartApprox_contDiff 0 δ).differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt

private theorem positivePart_gradient_error_decomposition
    (s a g D : ℝ) :
    s * a - D = s * (a - g) + (s * g - D) := by
  ring

private theorem memLp_max_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : α → ℝ} (hw : MemLp w (2 : ℝ≥0∞) μ) :
    MemLp (fun x => max (w x) 0) (2 : ℝ≥0∞) μ := by
  refine MemLp.of_le hw ?_ ?_
  · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      hw.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (w x) 0 with hx | hx
    · simp only [max_eq_right hx, abs_zero, abs_nonneg]
    · simp only [max_eq_left hx, le_rfl]

private theorem hasWeakGradientOn_of_smooth_approximation
    {f : Vec d → ℝ} {Du : Vec d → Vec d} {φ : ℕ → Vec d → ℝ}
    (hf : MemL2On U f) (hDu : GradMemL2On U Du)
    (hφSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφCompact : ∀ n, HasCompactSupport (φ n))
    (hφSupport : ∀ n, tsupport (φ n) ⊆ U)
    (hvalue : Tendsto
      (fun n => eLpNorm (φ n - f) (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0))
    (hgrad : ∀ i, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (basisVec i) - Du x i)
        (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0)) :
    HasWeakGradientOn U f Du := by
  apply HasWeakGradientOn.of_tendsto_eLpNorm
    (uSeq := φ)
    (DuSeq := fun n x i => (fderiv ℝ (φ n) x) (basisVec i)) hf hDu
  · intro n
    exact (WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_toFun 2
  · intro n i
    exact (WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_partialDeriv i 2
  · intro n
    exact HasWeakGradientOn.of_contDiff ((hφSmooth n).of_le (by norm_num))
  · exact hvalue
  · exact hgrad

private theorem exists_positivePart_regularization_scale
    (φ : Vec d → ℝ)
    (hφCompact : HasCompactSupport φ)
    (hφMeas : AEStronglyMeasurable φ (volumeOn U)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      eLpNorm
          (fun x => smoothPositivePartApprox 0 δ (φ x) - max (φ x) 0)
          (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal ε := by
  let δSeq : ℕ → ℝ := fun n => 1 / (n + 1)
  let err : ℕ → Vec d → ℝ := fun n x =>
    smoothPositivePartApprox 0 (δSeq n) (φ x) - max (φ x) 0
  have hδPos : ∀ n, 0 < δSeq n := by
    intro n
    dsimp only [δSeq]
    positivity
  have hδTendsto : Tendsto δSeq atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have herrSupport : ∀ n, Function.support (err n) ⊆ tsupport φ := by
    intro n x hx
    by_contra hxt
    have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    simp [err, hzero, smoothPositivePartApprox] at hx
  have herrBound : ∀ n,
      eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U) ≤
        ENNReal.ofReal (2 * δSeq n) *
          (volumeOn U) (tsupport φ) ^ (1 / (2 : ℝ)) := by
    intro n
    apply eLpNorm_sub_le_of_dist_bdd (μ := volumeOn U) (p := (2 : ℝ≥0∞)) (by norm_num)
      isClosed_closure.measurableSet.nullMeasurableSet (mul_nonneg (by norm_num) (hδPos n).le)
    · have hsmooth : Continuous (smoothPositivePartApprox 0 (δSeq n)) :=
        (smoothPositivePartApprox_contDiff_one 0 (δSeq n)).continuous
      exact (hsmooth.comp_aestronglyMeasurable hφMeas).sub
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable hφMeas)
    · intro x
      rw [Real.dist_eq]
      simpa only [sub_zero] using
        abs_smoothPositivePartApprox_sub_le (c := 0) (hδPos n) (φ x)
    · exact (Function.support_comp_subset
        (smoothPositivePartApprox_eq_zero_of_le (hδPos n) le_rfl) φ).trans
        (subset_closure)
    · intro x hx
      by_contra hxt
      have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
      simp only [Function.mem_support, hzero, max_self] at hx
      exact hx rfl
  have hconv : Tendsto
      (fun n => eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le') herrBound
    have hfinite : (volumeOn U) (tsupport φ) ^ (1 / (2 : ℝ)) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hφCompact.measure_lt_top.ne)
    have hofReal : Tendsto (fun n => ENNReal.ofReal (2 * δSeq n)) atTop (𝓝 0) := by
      simpa only [δSeq, ENNReal.ofReal_zero, mul_zero] using
        ENNReal.tendsto_ofReal (hδTendsto.const_mul (2 : ℝ))
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hofReal (Or.inr hfinite)
  have heventNorm : ∀ᶠ n in atTop,
      eLpNorm (err n) (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal ε :=
    ((tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.2 hε)).mono fun _ => le_of_lt
  have heventScale : ∀ᶠ n in atTop, δSeq n ≤ ε :=
    ((tendsto_order.1 hδTendsto).2 _ hε).mono fun _ => le_of_lt
  obtain ⟨n, hnNorm, hnScale⟩ := (heventNorm.and heventScale).exists
  exact ⟨δSeq n, hδPos n, hnScale, hnNorm⟩

/-- A nonnegative `H¹` representative with an explicit supported smooth
approximation admits another such approximation whose members are
pointwise nonnegative.

The conclusion is certificate-level, so every downstream use retains the
actual smooth functions, their support, and both `L²` convergence fields. -/
theorem exists_positivePart_nonnegative_supportedSmoothApproximation
    (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation)
    (hgradZero : ∀ᵐ x ∂(volumeOn U),
      u.toFun x = 0 → u.grad x = 0) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x) 0) ∧
      v.grad = (fun x => {y | 0 < u.toFun y}.indicator u.grad x) ∧
      ∃ hv : v.SupportedSmoothApproximation,
        ∀ n x, 0 ≤ hv.approx n x := by
  have happroxMeas :
      ∀ n,
        AEStronglyMeasurable (happrox.approx n) (volumeOn U) := by
    intro n
    exact
      (happrox.toWeakTestFunction n).memLp_toFun
        (2 : ℝ≥0∞) |>.aestronglyMeasurable
  obtain ⟨σ, hσStrictMono, hσAeRaw⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      happrox.tendsto_value).exists_seq_tendsto_ae
  have hσAe :
      ∀ᵐ x ∂(volumeOn U),
        Tendsto
          (fun i => happrox.approx (σ i) x)
          atTop (𝓝 (u.toFun x)) := by
    simpa only [H1Function.toW1pFunction_toFun] using hσAeRaw
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hεPos : ∀ n, 0 < ε n := by
    intro n
    dsimp only [ε]
    positivity
  have hεTendsto : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscale : ∀ n, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε n ∧
      eLpNorm
          (fun x => smoothPositivePartApprox 0 δ (happrox.approx (σ n) x) -
            max (happrox.approx (σ n) x) 0)
          (2 : ℝ≥0∞) (volumeOn U) ≤ ENNReal.ofReal (ε n) := by
    intro n
    exact exists_positivePart_regularization_scale
      (happrox.approx (σ n))
      (happrox.approx_hasCompactSupport (σ n)) (happroxMeas (σ n)) (ε n) (hεPos n)
  let δ : ℕ → ℝ := fun n => Classical.choose (hscale n)
  have hδPos : ∀ n, 0 < δ n := fun n => (Classical.choose_spec (hscale n)).1
  have hδLe : ∀ n, δ n ≤ ε n := fun n => (Classical.choose_spec (hscale n)).2.1
  have hδTendsto : Tendsto δ atTop (𝓝 0) := by
    exact squeeze_zero (fun n => (hδPos n).le) hδLe hεTendsto
  let positiveApprox : ℕ → Vec d → ℝ :=
    fun n x =>
      smoothPositivePartApprox 0 (δ n)
        (happrox.approx (σ n) x)
  have hpositiveSmooth :
      ∀ n, ContDiff ℝ (⊤ : ℕ∞) (positiveApprox n) := by
    intro n
    exact
      (smoothPositivePartApprox_contDiff 0 (δ n)).comp
        (happrox.approx_smooth (σ n))
  have hpositiveCompact :
      ∀ n, HasCompactSupport (positiveApprox n) := by
    intro n
    exact
      (happrox.approx_hasCompactSupport (σ n)).comp_left
        (smoothPositivePartApprox_eq_zero_of_le
          (hδPos n) le_rfl)
  have hpositiveSupport :
      ∀ n, tsupport (positiveApprox n) ⊆ U := by
    intro n
    refine
      (closure_mono
        (Function.support_comp_subset
          (smoothPositivePartApprox_eq_zero_of_le
            (hδPos n) le_rfl)
          (happrox.approx (σ n)))).trans ?_
    exact happrox.approx_tsupport_subset (σ n)
  have hpositiveNonnegative :
      ∀ n x, 0 ≤ positiveApprox n x := by
    intro n x
    exact smoothPositivePartApprox_nonneg
      (hδPos n) (happrox.approx (σ n) x)
  let valueRegularizationError : ℕ → Vec d → ℝ :=
    fun n x =>
      positiveApprox n x -
        max (happrox.approx (σ n) x) 0
  have hvalueRegularizationErrorMeas :
      ∀ n,
        AEStronglyMeasurable
          (valueRegularizationError n) (volumeOn U) := by
    intro n
    exact
      (hpositiveSmooth n).continuous.aestronglyMeasurable.sub
        (((happrox.approx_smooth (σ n)).continuous.max
          continuous_const).aestronglyMeasurable)
  have hvalueRegularizationErrorTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (valueRegularizationError n)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      (show Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) from ?_)
      (fun n => zero_le') (fun n => ?_)
    · simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hεTendsto
    · simpa only [valueRegularizationError, positiveApprox] using
        (Classical.choose_spec (hscale n)).2.2
  let valuePositivePartError : ℕ → Vec d → ℝ :=
    fun n x =>
      max (happrox.approx (σ n) x) 0 - max (u.toFun x) 0
  have hvaluePositivePartErrorMeas :
      ∀ n,
        AEStronglyMeasurable
          (valuePositivePartError n) (volumeOn U) := by
    intro n
    exact
      (((happrox.approx_smooth (σ n)).continuous.max
        continuous_const).aestronglyMeasurable).sub
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable
          u.memL2.aestronglyMeasurable)
  have hvaluePositivePartErrorBound :
      ∀ n,
        eLpNorm
            (valuePositivePartError n)
            (2 : ℝ≥0∞) (volumeOn U) ≤
          eLpNorm
            (fun x =>
              happrox.approx (σ n) x - u.toFun x)
            (2 : ℝ≥0∞) (volumeOn U) := by
    intro n
    apply eLpNorm_mono_ae (hvaluePositivePartErrorMeas n)
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |valuePositivePartError n x| =
          |max (happrox.approx (σ n) x) 0 -
            max (u.toFun x) 0| := by
        rfl
      _ ≤ |happrox.approx (σ n) x - u.toFun x| :=
        abs_max_sub_max_le_abs
          (happrox.approx (σ n) x) (u.toFun x) 0
  have hvaluePositivePartErrorTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (valuePositivePartError n)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (happrox.tendsto_value.comp
          hσStrictMono.tendsto_atTop)
        (fun _ => zero_le')
        hvaluePositivePartErrorBound
  have hvalueTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x => positiveApprox n x - max (u.toFun x) 0)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm
                (valueRegularizationError n)
                (2 : ℝ≥0∞) (volumeOn U) +
              eLpNorm
                (valuePositivePartError n)
                (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [zero_add] using
        hvalueRegularizationErrorTendsto.add
          hvaluePositivePartErrorTendsto
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hsum
        (fun _ => zero_le')
        (fun n => by
          have hdecomp :
              (fun x => positiveApprox n x - max (u.toFun x) 0) =
                valueRegularizationError n +
                  valuePositivePartError n := by
            funext x
            simp only [valueRegularizationError,
              valuePositivePartError, Pi.add_apply]
            ring
          rw [hdecomp]
          exact
            eLpNorm_add_le
              (by norm_num))
  let Du : Vec d → Vec d := fun x => {y | 0 < u.toFun y}.indicator u.grad x
  have hDuCoord : ∀ x i, Du x i = (if 0 < u.toFun x then 1 else 0) * u.grad x i := by
    intro x i
    by_cases hx : 0 < u.toFun x
    · simp [Du, Set.indicator_apply, hx]
    · simp [Du, Set.indicator_apply, hx]
  have hDuMem : GradMemL2On U Du := by
    intro i
    refine MemLp.of_le (u.grad_memL2 i) ?_ ?_
    · rw [show (fun x => Du x i) =
          {x | 0 < u.toFun x}.indicator (fun x => u.grad x i) by
          funext x; rw [hDuCoord]; by_cases hx : 0 < u.toFun x <;> simp [hx]]
      have hs : NullMeasurableSet {x | 0 < u.toFun x} (volumeOn U) := by
        change NullMeasurableSet (u.toFun ⁻¹' Set.Ioi 0) (volumeOn U)
        exact u.memL2.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage
          measurableSet_Ioi
      exact (u.grad_memL2 i).aestronglyMeasurable.indicator₀ hs
    · filter_upwards with x
      rw [hDuCoord]
      split_ifs <;> simp
  have hgradTendsto :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (positiveApprox n) x) (basisVec i) -
                  Du x i)
              (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    let first : ℕ → Vec d → ℝ :=
      fun n x =>
        smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
            u.grad x i)
    let second : ℕ → Vec d → ℝ :=
      fun n x =>
        smoothPositivePartStep 0 (δ n) (happrox.approx (σ n) x) *
          u.grad x i - Du x i
    have hfirstMeas :
        ∀ n,
          AEStronglyMeasurable (first n) (volumeOn U) := by
      intro n
      exact
        ((smoothPositivePartStep_continuous 0 (δ n))
          |>.comp_aestronglyMeasurable
            (happroxMeas (σ n))).mul
          (((happrox.toWeakTestFunction (σ n)).memLp_partialDeriv
              i (2 : ℝ≥0∞)).aestronglyMeasurable.sub
            (u.grad_memL2 i).aestronglyMeasurable)
    have hfirstBound :
        ∀ n,
          eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U) ≤
            eLpNorm
              (fun x =>
                (fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                  u.grad x i)
              (2 : ℝ≥0∞) (volumeOn U) := by
      intro n
      apply eLpNorm_mono_ae (hfirstMeas n)
      filter_upwards with x
      simp only [first, norm_mul, Real.norm_eq_abs]
      calc
        |smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x)| *
              ‖(fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                u.grad x i‖ ≤
            1 *
              ‖(fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                u.grad x i‖ :=
          mul_le_mul_of_nonneg_right
            (abs_smoothPositivePartStep_le_one
              0 (δ n) (happrox.approx (σ n) x))
            (norm_nonneg _)
        _ = _ := one_mul _
    have hfirstTendsto :
        Tendsto
          (fun n =>
            eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (happrox.tendsto_grad i |>.comp
          hσStrictMono.tendsto_atTop)
        (fun _ => zero_le') hfirstBound
    have hsecondMeas :
        ∀ n,
          AEStronglyMeasurable (second n) (volumeOn U) := by
      intro n
      exact
        (((smoothPositivePartStep_continuous 0 (δ n))
          |>.comp_aestronglyMeasurable
            (happroxMeas (σ n))).mul
          (u.grad_memL2 i).aestronglyMeasurable).sub
          (hDuMem i).aestronglyMeasurable
    have hsecondBound :
        ∀ n, ∀ᵐ x ∂(volumeOn U),
          ‖second n x‖ ≤ ‖(2 : ℝ) * u.grad x i‖ := by
      intro n
      filter_upwards with x
      simp only [second, hDuCoord, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      split_ifs with hx
      · rw [one_mul]
        nth_rewrite 2 [← one_mul (u.grad x i)]
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (by
          have hs0 := smoothPositivePartStep_nonneg 0 (δ n) (happrox.approx (σ n) x)
          have hs1 := smoothPositivePartStep_le_one 0 (δ n) (happrox.approx (σ n) x)
          rw [abs_of_nonpos (sub_nonpos.mpr hs1)]
          linarith) (abs_nonneg _)
      · rw [zero_mul, sub_zero, abs_mul]
        exact mul_le_mul_of_nonneg_right
          ((abs_smoothPositivePartStep_le_one _ _ _).trans (by norm_num)) (abs_nonneg _)
    have hsecondAe :
        ∀ᵐ x ∂(volumeOn U),
          Tendsto (fun n => second n x) atTop (𝓝 0) := by
      filter_upwards [hσAe, hgradZero] with x hx hzero
      by_cases hpos : 0 < u.toFun x
      · have happ :
            ∀ᶠ n in atTop,
              u.toFun x / 2 <
                happrox.approx (σ n) x :=
          (tendsto_order.1 hx).1 _ (by linarith)
        have hscale :
            ∀ᶠ n in atTop,
              δ n < u.toFun x / 4 :=
          (tendsto_order.1 hδTendsto).2 _ (by linarith)
        have heventually :
            ∀ᶠ n in atTop, second n x = 0 := by
          filter_upwards [happ, hscale] with n hn hδn
          have hstep :
              smoothPositivePartStep 0 (δ n)
                  (happrox.approx (σ n) x) = 1 :=
            smoothPositivePartStep_eq_one
              (hδPos n) (by linarith)
          simp only [second, hstep, hDuCoord, if_pos hpos, one_mul, sub_self]
        exact
          Tendsto.congr'
            (heventually.mono fun _ hn => hn.symm)
            tendsto_const_nhds
      · by_cases hneg : u.toFun x < 0
        · have happ : ∀ᶠ n in atTop, happrox.approx (σ n) x < u.toFun x / 2 :=
            (tendsto_order.1 hx).2 _ (by linarith)
          have heventually : ∀ᶠ n in atTop, second n x = 0 := by
            filter_upwards [happ] with n hn
            have hδn := hδPos n
            have hstep := smoothPositivePartStep_eq_zero hδn (by linarith :
              happrox.approx (σ n) x ≤ 0 + δ n)
            simp only [second, hstep, zero_mul, hDuCoord, if_neg hpos, sub_zero]
          exact Tendsto.congr' (heventually.mono fun _ hn => hn.symm) tendsto_const_nhds
        · have huZero : u.toFun x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
          have hg : u.grad x i = 0 := by rw [hzero huZero]; rfl
          simp only [second, hg, mul_zero, hDuCoord, if_neg hpos, sub_zero]
          exact tendsto_const_nhds
    have hsecondTendsto :
        Tendsto
          (fun n =>
            eLpNorm (second n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      exact tendsto_eLpNorm_two_zero_of_ae_dominated
        hsecondMeas ((u.grad_memL2 i).const_mul 2)
        hsecondBound hsecondAe
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U) +
              eLpNorm (second n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [zero_add] using
        hfirstTendsto.add hsecondTendsto
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hsum
        (fun _ => zero_le')
        (fun n => by
          have hdecomp :
              (fun x =>
                (fderiv ℝ (positiveApprox n) x) (basisVec i) -
                  Du x i) =
                first n + second n := by
            funext x
            have hchain :
                (fderiv ℝ (positiveApprox n) x) (basisVec i) =
                  smoothPositivePartStep 0 (δ n)
                      (happrox.approx (σ n) x) *
                    (fderiv ℝ (happrox.approx (σ n)) x)
                      (basisVec i) := by
              exact fderiv_smoothPositivePartApprox_comp_basisVec
                (happrox.approx_smooth (σ n)) x i
            rw [hchain]
            simp only [first, second, Pi.add_apply]
            exact positivePart_gradient_error_decomposition _ _ _ _
          rw [hdecomp]
          exact
            eLpNorm_add_le
              (by norm_num))
  let f : Vec d → ℝ := fun x => max (u.toFun x) 0
  have hfMem : MemL2On U f := by
    exact memLp_max_zero u.memL2
  have hweak : HasWeakGradientOn U f Du := by
    apply hasWeakGradientOn_of_smooth_approximation hfMem hDuMem
      hpositiveSmooth hpositiveCompact hpositiveSupport
    · change Tendsto
        (fun n => eLpNorm (fun x => positiveApprox n x - max (u.toFun x) 0)
          (2 : ℝ≥0∞) (volumeOn U)) atTop (𝓝 0)
      exact hvalueTendsto
    · exact hgradTendsto
  let v : H1Function U :=
    { toFun := f
      grad := Du
      memL2 := hfMem
      gradMemL2 := hDuMem
      hasWeakGradient := hweak }
  refine ⟨v, rfl, rfl, ?_⟩
  let hv : v.SupportedSmoothApproximation :=
    { approx := positiveApprox
      approx_smooth := hpositiveSmooth
      approx_hasCompactSupport := hpositiveCompact
      approx_tsupport_subset := hpositiveSupport
      tendsto_value := hvalueTendsto
      tendsto_grad := hgradTendsto }
  exact ⟨hv, hpositiveNonnegative⟩

/-- The positive part of an explicitly approximable `H¹` representative
retains an explicit supported smooth approximation. -/
theorem exists_positivePart_supportedSmoothApproximation
    (happrox : u.SupportedSmoothApproximation)
    (hgradZero : ∀ᵐ x ∂(volumeOn U),
      u.toFun x = 0 → u.grad x = 0) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x) 0) ∧
      v.grad = (fun x => {y | 0 < u.toFun y}.indicator u.grad x) ∧
      Nonempty v.SupportedSmoothApproximation := by
  obtain ⟨v, hvValue, hvGrad, hv, _⟩ :=
    exists_positivePart_nonnegative_supportedSmoothApproximation
      u happrox hgradZero
  exact ⟨v, hvValue, hvGrad, ⟨hv⟩⟩

end H1Function

end PDE
