module

public import PDEFoundation.Sobolev.W1p.Composition
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Positive-part truncation in `W^{1,p}`

This file proves positive-part truncation on bounded open convex domains for
every finite exponent `p ≥ 1`.  The construction uses one-sided smooth
approximations and the closed representative `W^{1,p}` graph, rather than a
general Lipschitz chain rule.

## Main definitions

- `smoothPositivePartStep`: a smooth approximation of the indicator of
  `(c, ∞)`.
- `smoothPositivePartApprox`: its antiderivative, approximating
  `t ↦ max (t - c) 0`.
- `W1pFunction.positivePartSubConst`: the representative
  `x ↦ max (u x - c) 0`.

## Main results

- `W1pFunction.positivePartSubConst_grad`: the exact representative gradient
  `1_{\{u>c\}} ∇u`.
- `W1pFunction.eLpNormOn_positivePartSubConst_toFun_le`: value contraction
  with constant one.
- `W1pFunction.eLpNormOn_positivePartSubConst_grad_coord_le`: contraction of
  every native gradient coordinate with constant one.

The strict superlevel set in the gradient formula is selected by the one-sided
smooth approximation.  No null-preimage or level-set theorem is assumed.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-! ## One-sided smooth approximations -/

/-- A smooth step which is zero below `c + δ`, one above `c + 2δ`, and takes
values in `[0, 1]`. -/
noncomputable def smoothPositivePartStep (c δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t - c) / δ - 1)

/-- The one-sided smooth approximation to `t ↦ max (t - c) 0` obtained by
integrating `smoothPositivePartStep`. -/
noncomputable def smoothPositivePartApprox (c δ t : ℝ) : ℝ :=
  ∫ s in c..t, smoothPositivePartStep c δ s

theorem smoothPositivePartStep_contDiff (c δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositivePartStep c δ) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_id.sub contDiff_const).div_const δ).sub contDiff_const)

theorem smoothPositivePartStep_continuous (c δ : ℝ) :
    Continuous (smoothPositivePartStep c δ) :=
  (smoothPositivePartStep_contDiff c δ).continuous

theorem smoothPositivePartStep_nonneg (c δ t : ℝ) :
    0 ≤ smoothPositivePartStep c δ t :=
  Real.smoothTransition.nonneg _

theorem smoothPositivePartStep_le_one (c δ t : ℝ) :
    smoothPositivePartStep c δ t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem abs_smoothPositivePartStep_le_one (c δ t : ℝ) :
    |smoothPositivePartStep c δ t| ≤ 1 := by
  rw [abs_of_nonneg (smoothPositivePartStep_nonneg c δ t)]
  exact smoothPositivePartStep_le_one c δ t

theorem smoothPositivePartStep_eq_zero
    {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c + δ) :
    smoothPositivePartStep c δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, div_le_one hδ]
  linarith

theorem smoothPositivePartStep_eq_one
    {c δ t : ℝ} (hδ : 0 < δ) (ht : c + 2 * δ ≤ t) :
    smoothPositivePartStep c δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]
  linarith

theorem smoothPositivePartStep_intervalIntegrable (c δ a b : ℝ) :
    IntervalIntegrable (smoothPositivePartStep c δ) volume a b :=
  (smoothPositivePartStep_continuous c δ).intervalIntegrable a b

theorem smoothPositivePartApprox_hasDerivAt (c δ t : ℝ) :
    HasDerivAt (smoothPositivePartApprox c δ)
      (smoothPositivePartStep c δ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (smoothPositivePartStep_intervalIntegrable c δ c t)
    ((smoothPositivePartStep_continuous c δ).stronglyMeasurableAtFilter _ _)
    (smoothPositivePartStep_continuous c δ).continuousAt

theorem deriv_smoothPositivePartApprox (c δ : ℝ) :
    deriv (smoothPositivePartApprox c δ) =
      smoothPositivePartStep c δ := by
  funext t
  exact (smoothPositivePartApprox_hasDerivAt c δ t).deriv

theorem smoothPositivePartApprox_contDiff_one (c δ : ℝ) :
    ContDiff ℝ 1 (smoothPositivePartApprox c δ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => ?_, ?_⟩
  · exact (smoothPositivePartApprox_hasDerivAt c δ t).differentiableAt
  · rw [deriv_smoothPositivePartApprox]
    exact smoothPositivePartStep_continuous c δ

/-- The one-sided positive-part approximation is smooth to every order. -/
theorem smoothPositivePartApprox_contDiff (c δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositivePartApprox c δ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => ?_, ?_⟩
  · exact (smoothPositivePartApprox_hasDerivAt c δ t).differentiableAt
  · rw [deriv_smoothPositivePartApprox]
    exact smoothPositivePartStep_contDiff c δ

theorem abs_deriv_smoothPositivePartApprox_le (c δ t : ℝ) :
    |deriv (smoothPositivePartApprox c δ) t| ≤ 1 := by
  rw [deriv_smoothPositivePartApprox,
    abs_of_nonneg (smoothPositivePartStep_nonneg c δ t)]
  exact smoothPositivePartStep_le_one c δ t

/-- The smooth steps converge pointwise to the strict-superlevel indicator. -/
theorem tendsto_smoothPositivePartStep
    {c : ℝ} {δ : ℕ → ℝ} (hδPos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (t : ℝ) :
    Tendsto
      (fun n => smoothPositivePartStep c (δ n) t)
      atTop (𝓝 (if c < t then 1 else 0)) := by
  by_cases hct : c < t
  · rw [ite_eq_left hct]
    have heventually :
        ∀ᶠ n in atTop, smoothPositivePartStep c (δ n) t = 1 := by
      have hsmall :
          ∀ᶠ n in atTop, δ n < (t - c) / 2 :=
        (tendsto_order.1 hδ).2 _ (by linarith)
      filter_upwards [hsmall] with n hn
      exact smoothPositivePartStep_eq_one (hδPos n) (by linarith)
    exact
      Tendsto.congr'
        (heventually.mono fun _ hn => hn.symm)
        tendsto_const_nhds
  · rw [ite_eq_right hct]
    have heventually :
        ∀ᶠ n in atTop, smoothPositivePartStep c (δ n) t = 0 :=
      Filter.Eventually.of_forall fun n =>
        smoothPositivePartStep_eq_zero (hδPos n) (by
          push Not at hct
          linarith [(hδPos n).le])
    exact
      Tendsto.congr'
        (heventually.mono fun _ hn => hn.symm)
        tendsto_const_nhds

theorem abs_smoothPositivePartApprox_le (c δ t : ℝ) :
    |smoothPositivePartApprox c δ t| ≤ |t - c| := by
  rw [smoothPositivePartApprox, ← Real.norm_eq_abs]
  refine
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => ?_)).trans (one_mul _).le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (smoothPositivePartStep_nonneg c δ s)]
  exact smoothPositivePartStep_le_one c δ s

/-- The one-sided approximation vanishes at and below its truncation
threshold. -/
theorem smoothPositivePartApprox_eq_zero_of_le
    {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c) :
    smoothPositivePartApprox c δ t = 0 := by
  rw [smoothPositivePartApprox,
    ← intervalIntegral.integral_zero
      (a := c) (b := t) (μ := volume)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_ge ht] at hs
  exact
    smoothPositivePartStep_eq_zero hδ
      (by linarith [hs.2, le_of_lt hδ])

/-- The one-sided approximation to the positive part is pointwise
nonnegative. -/
theorem smoothPositivePartApprox_nonneg
    {c δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ smoothPositivePartApprox c δ t := by
  rcases le_total t c with htc | hct
  · rw [smoothPositivePartApprox_eq_zero_of_le hδ htc]
  · rw [smoothPositivePartApprox]
    exact intervalIntegral.integral_nonneg hct
      (fun s _ => smoothPositivePartStep_nonneg c δ s)

/-- The scalar approximation is uniformly within `2δ` of the positive part. -/
theorem abs_smoothPositivePartApprox_sub_le
    {c δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |smoothPositivePartApprox c δ t - max (t - c) 0| ≤ 2 * δ := by
  rcases le_or_gt t c with htc | htc
  · have hzero : smoothPositivePartApprox c δ t = 0 := by
      exact smoothPositivePartApprox_eq_zero_of_le hδ htc
    rw [hzero, max_eq_right (by linarith), sub_zero, abs_zero]
    linarith
  · rw [max_eq_left (by linarith)]
    have hle :
        smoothPositivePartApprox c δ t ≤ t - c := by
      rw [smoothPositivePartApprox]
      calc
        (∫ s in c..t, smoothPositivePartStep c δ s) ≤
            ∫ _ in c..t, (1 : ℝ) :=
          intervalIntegral.integral_mono_on htc.le
            (smoothPositivePartStep_intervalIntegrable c δ c t)
            intervalIntegrable_const
            (fun s _ => smoothPositivePartStep_le_one c δ s)
        _ = t - c := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hge :
        t - c - 2 * δ ≤ smoothPositivePartApprox c δ t := by
      by_cases htwo : c + 2 * δ ≤ t
      · have hsplit :
            smoothPositivePartApprox c δ t =
              (∫ s in c..(c + 2 * δ),
                smoothPositivePartStep c δ s) +
              ∫ s in (c + 2 * δ)..t,
                smoothPositivePartStep c δ s := by
            rw [smoothPositivePartApprox]
            exact
              (intervalIntegral.integral_add_adjacent_intervals
                (smoothPositivePartStep_intervalIntegrable c δ _ _)
                (smoothPositivePartStep_intervalIntegrable c δ _ _)).symm
        have htail :
            (∫ s in (c + 2 * δ)..t,
              smoothPositivePartStep c δ s) =
              t - (c + 2 * δ) := by
          rw [show
            (∫ s in (c + 2 * δ)..t,
              smoothPositivePartStep c δ s) =
              ∫ _ in (c + 2 * δ)..t, (1 : ℝ) from
            intervalIntegral.integral_congr
              (fun s hs => by
                rw [Set.uIcc_of_le htwo] at hs
                exact smoothPositivePartStep_eq_one hδ hs.1),
            intervalIntegral.integral_const, smul_eq_mul, mul_one]
        have hhead :
            0 ≤ ∫ s in c..(c + 2 * δ),
              smoothPositivePartStep c δ s :=
          intervalIntegral.integral_nonneg (by linarith)
            (fun s _ => smoothPositivePartStep_nonneg c δ s)
        rw [hsplit, htail]
        linarith
      · push Not at htwo
        have hnonneg :
            0 ≤ smoothPositivePartApprox c δ t :=
          intervalIntegral.integral_nonneg htc.le
            (fun s _ => smoothPositivePartStep_nonneg c δ s)
        linarith
    rw [abs_le]
    constructor <;> linarith

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Value integrability, gradient integrability, and weak differentiation for truncation. -/
theorem positivePartSubConst_data
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    MemLpOn U p (fun x => max (u.toFun x - c) 0) ∧
      GradMemLpOn U p
        (fun x => {y | c < u.toFun y}.indicator u.grad x) ∧
      HasWeakGradientOn U
        (fun x => max (u.toFun x - c) 0)
        (fun x => {y | c < u.toFun y}.indicator u.grad x) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδPos : ∀ n, 0 < δ n := by
    intro n
    positivity
  have hδTendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f : Vec d → ℝ :=
    fun x => max (u.toFun x - c) 0
  let Du : Vec d → Vec d :=
    fun x => {y | c < u.toFun y}.indicator u.grad x
  let valueSeq : ℕ → Vec d → ℝ :=
    fun n x => smoothPositivePartApprox c (δ n) (u.toFun x)
  let gradSeq : ℕ → Vec d → Vec d :=
    fun n x i =>
      smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i
  have hDuCoord :
      ∀ x i,
        Du x i =
          (if c < u.toFun x then (1 : ℝ) else 0) *
            u.grad x i := by
    intro x i
    by_cases hx : c < u.toFun x
    · have hxMem : x ∈ {y | c < u.toFun y} := hx
      change
        ({y | c < u.toFun y}.indicator u.grad x) i =
          (if c < u.toFun x then 1 else 0) * u.grad x i
      rw [Set.indicator_of_mem hxMem, ite_eq_left hx, one_mul]
    · have hxNotMem : x ∉ {y | c < u.toFun y} := hx
      change
        ({y | c < u.toFun y}.indicator u.grad x) i =
          (if c < u.toFun x then 1 else 0) * u.grad x i
      rw [Set.indicator_of_notMem hxNotMem,
        Pi.zero_apply, ite_eq_right hx, zero_mul]
  have hvalueSeqAesm :
      ∀ n,
        AEStronglyMeasurable (valueSeq n) (volumeOn U) := by
    intro n
    exact
      (smoothPositivePartApprox_contDiff_one c (δ n)).continuous
        |>.comp_aestronglyMeasurable u.memLp.aestronglyMeasurable
  have hgradSeqAesm :
      ∀ i n,
        AEStronglyMeasurable
          (fun x => gradSeq n x i) (volumeOn U) := by
    intro i n
    exact
      ((smoothPositivePartStep_continuous c (δ n))
        |>.comp_aestronglyMeasurable
          u.memLp.aestronglyMeasurable).mul
        (u.grad_memLp i).aestronglyMeasurable
  have hvalueTendsto :
      ∀ x,
        Tendsto (fun n => valueSeq n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have htwo :
        Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδTendsto.const_mul (2 : ℝ)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htwo
    rw [Real.norm_eq_abs]
    exact
      abs_smoothPositivePartApprox_sub_le
        (hδPos n) (u.toFun x)
  have hgradTendsto :
      ∀ i x,
        Tendsto
          (fun n => gradSeq n x i)
          atTop (𝓝 (Du x i)) := by
    intro i x
    have htendsto :=
      (tendsto_smoothPositivePartStep
        (c := c) hδPos hδTendsto (u.toFun x)).mul_const
        (u.grad x i)
    simpa only [gradSeq, hDuCoord x i] using htendsto
  have hfAesm :
      AEStronglyMeasurable f (volumeOn U) :=
    (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable u.memLp.aestronglyMeasurable)
  have hfMem : MemLpOn U p f := by
    refine
      MemLp.of_le
        (u.memLp.sub (memLp_const c)) hfAesm ?_
    filter_upwards with x
    simp only [f, Real.norm_eq_abs, Pi.sub_apply]
    rcases le_or_gt (u.toFun x - c) 0 with hnonpos | hpos
    · simp only [max_eq_right hnonpos, abs_zero]
      exact abs_nonneg (u.toFun x - c)
    · rw [max_eq_left hpos.le]
  have hDuAesm :
      ∀ i,
        AEStronglyMeasurable
          (fun x => Du x i) (volumeOn U) := by
    intro i
    exact
      aestronglyMeasurable_of_tendsto_ae atTop
        (hgradSeqAesm i)
        (Filter.Eventually.of_forall (hgradTendsto i))
  have hDuMem : GradMemLpOn U p Du := by
    intro i
    refine MemLp.of_le (u.grad_memLp i) (hDuAesm i) ?_
    filter_upwards with x
    rw [hDuCoord x i]
    split_ifs
    · simpa only [one_mul] using
        (le_rfl : ‖u.grad x i‖ ≤ ‖u.grad x i‖)
    · simpa only [zero_mul, norm_zero] using
        norm_nonneg (u.grad x i)
  have hvalueSeqMem :
      ∀ n, MemLpOn U p (valueSeq n) := by
    intro n
    refine
      MemLp.of_le
        (u.memLp.sub (memLp_const c))
        (hvalueSeqAesm n) ?_
    filter_upwards with x
    simp only [valueSeq, Pi.sub_apply,
      Real.norm_eq_abs]
    exact
      abs_smoothPositivePartApprox_le c (δ n) (u.toFun x)
  have hgradSeqMem :
      ∀ n, GradMemLpOn U p (gradSeq n) := by
    intro n i
    change
      MemLp (fun x => gradSeq n x i)
        p (volumeOn U)
    refine
      MemLp.of_le
        (f := fun x => gradSeq n x i)
        (g := fun x => u.grad x i)
        (u.grad_memLp i)
        (hgradSeqAesm i n) ?_
    filter_upwards with x
    change
      ‖smoothPositivePartStep c (δ n) (u.toFun x) *
          u.grad x i‖ ≤
        ‖u.grad x i‖
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |smoothPositivePartStep c (δ n) (u.toFun x)| *
          ‖u.grad x i‖ ≤
          1 * ‖u.grad x i‖ :=
        mul_le_mul_of_nonneg_right
          (abs_smoothPositivePartStep_le_one
            c (δ n) (u.toFun x))
          (norm_nonneg (u.grad x i))
      _ = ‖u.grad x i‖ := one_mul _
  have hweakSeq :
      ∀ n,
        HasWeakGradientOn U (valueSeq n) (gradSeq n) := by
    intro n
    simpa only [valueSeq, gradSeq,
      deriv_smoothPositivePartApprox] using
      hasWeakGradient_comp_contDiff_of_deriv_bounded
        hU hp hpTop u
        (smoothPositivePartApprox_contDiff_one c (δ n))
        zero_le_one
        (abs_deriv_smoothPositivePartApprox_le c (δ n))
  have hvalueConv :
      Tendsto
        (fun n =>
          eLpNorm (valueSeq n - f) p (volumeOn U))
        atTop (𝓝 0) :=
    tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
      hp hpTop hvalueSeqAesm hfMem
      (u.memLp.sub (memLp_const c))
      (fun n => Filter.Eventually.of_forall fun x => by
        simp only [valueSeq, Pi.sub_apply, Real.norm_eq_abs]
        exact
          abs_smoothPositivePartApprox_le c (δ n) (u.toFun x))
      (Filter.Eventually.of_forall hvalueTendsto)
  have hgradConv :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => gradSeq n x i - Du x i)
              p (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    have hbound :
        ∀ n, ∀ᵐ x ∂(volumeOn U),
          ‖gradSeq n x i‖ ≤ ‖u.grad x i‖ := by
      intro n
      filter_upwards with x
      change
        ‖smoothPositivePartStep c (δ n) (u.toFun x) *
            u.grad x i‖ ≤
          ‖u.grad x i‖
      rw [norm_mul, Real.norm_eq_abs]
      calc
        |smoothPositivePartStep c (δ n) (u.toFun x)| *
            ‖u.grad x i‖ ≤
            1 * ‖u.grad x i‖ :=
          mul_le_mul_of_nonneg_right
            (abs_smoothPositivePartStep_le_one
              c (δ n) (u.toFun x))
            (norm_nonneg (u.grad x i))
        _ = ‖u.grad x i‖ := one_mul _
    exact
      tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
        hp hpTop (hgradSeqAesm i) (hDuMem i)
        (u.grad_memLp i) hbound
        (Filter.Eventually.of_forall (hgradTendsto i))
  have hweak :
      HasWeakGradientOn U f Du :=
    HasWeakGradientOn.of_tendsto_eLpNorm
      hfMem hDuMem hvalueSeqMem hgradSeqMem hweakSeq
      hvalueConv hgradConv
  exact ⟨hfMem, hDuMem, hweak⟩

/-- Positive-part truncation of a representative `W^{1,p}` function at a
constant level.  Both the value and gradient representatives are literal. -/
noncomputable def positivePartSubConst
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    W1pFunction U p where
  toFun := fun x => max (u.toFun x - c) 0
  grad := fun x =>
    {y | c < u.toFun y}.indicator u.grad x
  memLp :=
    (positivePartSubConst_data hU hp hpTop u c).1
  gradMemLp :=
    (positivePartSubConst_data hU hp hpTop u c).2.1
  hasWeakGradient :=
    (positivePartSubConst_data hU hp hpTop u c).2.2

@[simp]
theorem positivePartSubConst_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.positivePartSubConst hU hp hpTop c).toFun =
      fun x => max (u.toFun x - c) 0 :=
  rfl

@[simp]
theorem positivePartSubConst_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.positivePartSubConst hU hp hpTop c).grad =
      fun x => {y | c < u.toFun y}.indicator u.grad x :=
  rfl

/-- The literal gradient representative gives the advertised indicator formula
almost everywhere. -/
theorem positivePartSubConst_grad_ae
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U),
      (u.positivePartSubConst hU hp hpTop c).grad x =
        {y | c < u.toFun y}.indicator u.grad x :=
  Filter.Eventually.of_forall fun _ => rfl

/-- Positive-part truncation contracts the value seminorm, relative to the
shifted function `u - c`, with constant one. -/
theorem eLpNormOn_positivePartSubConst_toFun_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    eLpNormOn U p
        (u.positivePartSubConst hU hp hpTop c).toFun ≤
      eLpNormOn U p (fun x => u.toFun x - c) := by
  apply eLpNorm_mono
    (u.positivePartSubConst hU hp hpTop c).memLp.aestronglyMeasurable
  intro x
  simp only [positivePartSubConst_toFun,
    Real.norm_eq_abs]
  rcases le_or_gt (u.toFun x - c) 0 with hnonpos | hpos
  · simp only [max_eq_right hnonpos, abs_zero]
    exact abs_nonneg (u.toFun x - c)
  · rw [max_eq_left hpos.le]

/-- Positive-part truncation contracts every native coordinate-gradient
seminorm with constant one. -/
theorem eLpNormOn_positivePartSubConst_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.positivePartSubConst hU hp hpTop c).grad x i) ≤
      eLpNormOn U p (fun x => u.grad x i) := by
  apply eLpNorm_mono
    ((u.positivePartSubConst hU hp hpTop c).gradMemLp i).aestronglyMeasurable
  intro x
  by_cases hx : c < u.toFun x
  · have hxMem : x ∈ {y | c < u.toFun y} := hx
    change
      ‖({y | c < u.toFun y}.indicator u.grad x) i‖ ≤
        ‖u.grad x i‖
    rw [Set.indicator_of_mem hxMem]
  · have hxNotMem : x ∉ {y | c < u.toFun y} := hx
    change
      ‖({y | c < u.toFun y}.indicator u.grad x) i‖ ≤
        ‖u.grad x i‖
    rw [Set.indicator_of_notMem hxNotMem, Pi.zero_apply]
    simpa only [norm_zero] using norm_nonneg (u.grad x i)

/-- Positive-part truncation contracts the full Euclidean gradient seminorm
with exact constant one. -/
theorem euclideanFieldELpNormOn_positivePartSubConst_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    euclideanFieldELpNormOn U p
        (u.positivePartSubConst hU hp hpTop c).grad ≤
      euclideanFieldELpNormOn U p u.grad := by
  apply euclideanFieldELpNormOn_mono_ae
    (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
      ((u.positivePartSubConst hU hp hpTop c).gradMemLp i).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    rw [positivePartSubConst_grad]
    change vecEuclideanNorm ({y | c < u.toFun y}.indicator u.grad x) ≤
      vecEuclideanNorm (u.grad x)
    by_cases hx : c < u.toFun x
    · rw [Set.indicator_of_mem
        (s := {y | c < u.toFun y}) (a := x) hx]
    · rw [Set.indicator_of_notMem
        (s := {y | c < u.toFun y}) (a := x) hx]
      have hzero : vecEuclideanNorm (0 : Vec d) = 0 :=
        vecEuclideanNorm_eq_zero_iff.mpr rfl
      rw [hzero]
      exact vecEuclideanNorm_nonneg (u.grad x)

/-- On a positive finite-volume domain, positive-part truncation contracts
the normalized full Euclidean gradient seminorm with exact constant one. -/
theorem euclideanFieldELpMeanNormOn_positivePartSubConst_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    euclideanFieldELpMeanNormOn U p
        (u.positivePartSubConst hU hp hpTop c).grad ≤
      euclideanFieldELpMeanNormOn U p u.grad := by
  have hvolumePos :
      0 < volume U ^ (1 / p).toReal :=
    ENNReal.rpow_pos hUPos hUTop.ne
  have hvolumeTop :
      volume U ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hUPos.ne' hUTop.ne
  have hraw :=
    euclideanFieldELpNormOn_positivePartSubConst_grad_le
      hU hp hpTop u c
  rw [euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop,
    euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop] at hraw
  exact
    (ENNReal.mul_le_mul_iff_right
      hvolumePos.ne' hvolumeTop).mp <| by
        simpa only [mul_assoc, mul_left_comm] using hraw

/-- Existential facade matching the representative specification commonly
used by downstream `H¹` developments. -/
theorem exists_w1p_max_sub_const
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    ∃ v : W1pFunction U p,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      ∀ᵐ x ∂(volumeOn U),
        v.grad x =
          {y | c < u.toFun y}.indicator u.grad x :=
  ⟨u.positivePartSubConst hU hp hpTop c, rfl,
    Filter.Eventually.of_forall fun _ => rfl⟩

end W1pFunction

end PDE
