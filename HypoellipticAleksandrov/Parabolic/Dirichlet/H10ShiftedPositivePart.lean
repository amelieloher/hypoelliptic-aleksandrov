module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenPositivePartApproximation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity

/-!
# Shifted positive parts in spatial `H¹₀`

This module constructs `(u - k)₊` without representing the nonzero constant
`k` as an element of `H¹₀`.  The construction works on an arbitrary open set.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The shifted positive-part function has Lipschitz constant one. -/
theorem lipschitzWith_max_sub_zero (k : ℝ≥0) :
    LipschitzWith 1 (fun s : ℝ => max (s - (k : ℝ)) 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [show dist a b = |a - b| by rfl]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right] using
    abs_max_sub_max_le_abs (a - (k : ℝ)) (b - (k : ℝ)) 0

/-- A nonnegative shift sends zero to zero. -/
theorem max_sub_zero_at_zero (k : ℝ≥0) :
    max ((0 : ℝ) - (k : ℝ)) 0 = 0 := by
  rw [max_eq_right]
  exact sub_nonpos.mpr k.2

/-- The literal `L²` composition representing the shifted positive part. -/
def shiftedPositivePartValue
    (k : ℝ≥0) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  (lipschitzWith_max_sub_zero k).compLp (max_sub_zero_at_zero k) f

/-- Evaluation of the shifted positive-part `L²` composition. -/
theorem coeFn_shiftedPositivePartValue
    (k : ℝ≥0) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    shiftedPositivePartValue k f =ᵐ[PDE.volumeOn Ω]
      fun x => max (f x - (k : ℝ)) 0 := by
  simpa only [shiftedPositivePartValue, Function.comp_def] using
    (lipschitzWith_max_sub_zero k).coeFn_compLp (max_sub_zero_at_zero k) f

private theorem norm_shiftedPositivePartValue_le
    (k : ℝ≥0) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖shiftedPositivePartValue k f‖ ≤ ‖f‖ := by
  simpa only [shiftedPositivePartValue, NNReal.coe_one, one_mul] using
    (lipschitzWith_max_sub_zero k).norm_compLp_le
      (max_sub_zero_at_zero k) f

private def h1FunctionOfH10
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) : PDE.H1Function Ω where
  toFun := valueCLM hΩ u
  grad := fun x => (gradientCLM hΩ u x).ofLp
  memL2 := Lp.memLp _
  gradMemL2 := fun i => (Lp.memLp (gradientCLM hΩ u)).eval_piLp i
  hasWeakGradient := by
    intro i
    rw [PDE.hasWeakPartialDerivOn_iff_forall_testFunction]
    intro φ
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [PDE.weakGradientConstraint_apply_eq_integral, PDE.H1HilbertGraph.toH1Graph,
      PDE.H1HilbertGraph.value, PDE.H1HilbertGraph.gradient, PDE.volumeOn,
      WithLp.prodContinuousLinearEquiv_apply, WithLp.fst, WithLp.snd,
      valueCLM_apply, gradientCLM_apply] using
      PDE.W1pGraph.constraint_eq_zero
        (PDE.H1HilbertGraph.toH1Graph
          (u : PDE.H1HilbertGraph Ω)) i φ

private theorem h1FunctionOfH10_hasSupportedSmoothApproximation
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    Nonempty (h1FunctionOfH10 hΩ u).SupportedSmoothApproximation := by
  let ug := h10HilbertGraphContinuousLinearEquiv hΩ u
  rcases PDE.H10Graph.exists_tendsto_smooth hΩ ug with ⟨φ, hφ⟩
  let w := h1FunctionOfH10 hΩ u
  have hvalue : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.1)
      atTop (𝓝 (valueCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, valueCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  have hgradient : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2)
      atTop (𝓝 (gradientCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, gradientCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  refine ⟨{
    approx := fun n => (φ n).toFun
    approx_smooth := fun n => (φ n).contDiff
    approx_hasCompactSupport := fun n => (φ n).hasCompactSupport
    approx_tsupport_subset := fun n => (φ n).tsupport_subset
    tendsto_value := ?_
    tendsto_grad := ?_ }⟩
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (φ n).toFun) (fun n => (φ n).memLp_toFun (2 : ℝ≥0∞))
      w.toFun w.memL2).mp (by
        simpa only [w, h1FunctionOfH10,
          PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph,
          PDE.W1pFunction.toW1pGraph, PDE.W1pFunction.ofContDiff,
          Lp.toLp_coeFn, PDE.w1pGraphOfRepresentatives,
          PDE.weakGradientLpPairOfRepresentatives] using! hvalue)
  · intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))
      (fun n => (φ n).memLp_partialDeriv i (2 : ℝ≥0∞))
      (fun x => w.grad x i) (w.gradMemL2 i)).mp
    have heval := (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i).continuous.tendsto _ |>.comp hgradient
    have hseq : ∀ n,
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 =
          ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i)) := by
      intro n
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
          (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2,
        PDE.W1pFunction.coeFn_toW1pGraph_snd
          (PDE.W1pFunction.ofContDiff hΩ
            ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2),
        ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).coeFn_toLp] with x hc hg ht
      have hg' :
          ⇑(PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 x =
            PDE.toHilbertVecField
              (PDE.W1pFunction.ofContDiff hΩ
                ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2).grad x := by
        simpa only [PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph] using hg
      have ht' :
          ⇑(((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))) x =
            (fderiv ℝ (φ n).toFun x) (PDE.basisVec i) := by
        change ⇑(((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
          ((φ n).partialDeriv i)) x = _
        exact ht
      rw [hc, hg', ht']
      rfl
    have hlim : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ u) =
        (w.gradMemL2 i).toLp (fun x => w.grad x i) := by
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u),
        (w.gradMemL2 i).coeFn_toLp] with x hc ht
      rw [hc, ht]
      rfl
    rw [← hlim]
    simpa only [Function.comp_def, hseq] using heval

private theorem hasWeakGradientOn_of_smooth_approximation
    {f : PDE.Vec d → ℝ} {Du : PDE.Vec d → PDE.Vec d}
    {φ : ℕ → PDE.Vec d → ℝ}
    (hf : PDE.MemL2On Ω f) (hDu : PDE.GradMemL2On Ω Du)
    (hφSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφCompact : ∀ n, HasCompactSupport (φ n))
    (hφSupport : ∀ n, tsupport (φ n) ⊆ Ω)
    (hvalue : Tendsto
      (fun n => eLpNorm (φ n - f) (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0))
    (hgrad : ∀ i, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n) x) (PDE.basisVec i) - Du x i)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0)) :
    PDE.HasWeakGradientOn Ω f Du := by
  apply PDE.HasWeakGradientOn.of_tendsto_eLpNorm
    (uSeq := φ)
    (DuSeq := fun n x i => (fderiv ℝ (φ n) x) (PDE.basisVec i)) hf hDu
  · intro n
    exact (PDE.WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_toFun 2
  · intro n i
    exact (PDE.WeakTestFunction.mk (φ n) (hφSmooth n) (hφCompact n)
      (hφSupport n)).memLp_partialDeriv i 2
  · intro n
    exact PDE.HasWeakGradientOn.of_contDiff ((hφSmooth n).of_le (by norm_num))
  · exact hvalue
  · exact hgrad

private theorem exists_shifted_regularization_scale
    (φ : PDE.Vec d → ℝ) (hφCompact : HasCompactSupport φ)
    (hφMeas : AEStronglyMeasurable φ (PDE.volumeOn Ω))
    (k : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      eLpNorm
          (fun x => PDE.smoothPositivePartApprox (k : ℝ) δ (φ x) -
            max (φ x - (k : ℝ)) 0)
          (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤ ENNReal.ofReal ε := by
  let δSeq : ℕ → ℝ := fun n => 1 / (n + 1)
  let err : ℕ → PDE.Vec d → ℝ := fun n x =>
    PDE.smoothPositivePartApprox (k : ℝ) (δSeq n) (φ x) -
      max (φ x - (k : ℝ)) 0
  have hδPos : ∀ n, 0 < δSeq n := by
    intro n
    dsimp only [δSeq]
    positivity
  have hδTendsto : Tendsto δSeq atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have herrBound : ∀ n,
      eLpNorm (err n) (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤
        ENNReal.ofReal (2 * δSeq n) *
          (PDE.volumeOn Ω) (tsupport φ) ^ (1 / (2 : ℝ)) := by
    intro n
    apply eLpNorm_sub_le_of_dist_bdd (μ := PDE.volumeOn Ω)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      isClosed_closure.measurableSet.nullMeasurableSet (mul_nonneg (by norm_num) (hδPos n).le)
    · exact ((PDE.smoothPositivePartApprox_contDiff (k : ℝ) (δSeq n)).continuous
        |>.comp_aestronglyMeasurable hφMeas).sub
        (((continuous_id.sub continuous_const).max continuous_const)
          |>.comp_aestronglyMeasurable hφMeas)
    · intro x
      rw [Real.dist_eq]
      simpa only [sub_zero] using
        PDE.abs_smoothPositivePartApprox_sub_le (c := (k : ℝ)) (hδPos n) (φ x)
    · exact (Function.support_comp_subset
        (PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2) φ).trans
        subset_closure
    · intro x hx
      by_contra hxt
      have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
      have hmax : max ((0 : ℝ) - (k : ℝ)) 0 = 0 := max_sub_zero_at_zero k
      simp only [Function.mem_support, hzero] at hx
      exact hx hmax
  have hconv : Tendsto
      (fun n => eLpNorm (err n) (2 : ℝ≥0∞) (PDE.volumeOn Ω))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le') herrBound
    have hfinite : (PDE.volumeOn Ω) (tsupport φ) ^ (1 / (2 : ℝ)) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hφCompact.measure_lt_top.ne)
    have hofReal : Tendsto (fun n => ENNReal.ofReal (2 * δSeq n)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, mul_zero] using
        ENNReal.tendsto_ofReal (hδTendsto.const_mul (2 : ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hofReal (Or.inr hfinite)
  have heventNorm : ∀ᶠ n in atTop,
      eLpNorm (err n) (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤ ENNReal.ofReal ε :=
    ((tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.2 hε)).mono fun _ => le_of_lt
  have heventScale : ∀ᶠ n in atTop, δSeq n ≤ ε :=
    ((tendsto_order.1 hδTendsto).2 _ hε).mono fun _ => le_of_lt
  obtain ⟨n, hnNorm, hnScale⟩ := (heventNorm.and heventScale).exists
  exact ⟨δSeq n, hδPos n, hnScale, hnNorm⟩

private theorem memLp_max_sub_nonneg
    {w : PDE.Vec d → ℝ} (hw : MemLp w (2 : ℝ≥0∞) (PDE.volumeOn Ω))
    (k : ℝ≥0) :
    MemLp (fun x => max (w x - (k : ℝ)) 0) (2 : ℝ≥0∞) (PDE.volumeOn Ω) := by
  refine MemLp.of_le hw ?_ ?_
  · exact ((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable hw.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (w x) (k : ℝ) with hx | hx
    · rw [max_eq_right (sub_nonpos.mpr hx), abs_zero]
      exact abs_nonneg _
    · rw [max_eq_left (sub_nonneg.mpr hx)]
      rw [abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (k.2.trans hx)]
      exact sub_le_self _ k.2

private theorem fderiv_shifted_smooth_comp_basisVec
    {φ : PDE.Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : ℝ≥0) {δ : ℝ} (x : PDE.Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => PDE.smoothPositivePartApprox (k : ℝ) δ (φ y)) x)
        (PDE.basisVec i) =
      PDE.smoothPositivePartStep (k : ℝ) δ (φ x) *
        (fderiv ℝ φ x) (PDE.basisVec i) := by
  simpa only [PDE.deriv_smoothPositivePartApprox] using
    PDE.fderiv_comp_basisVec
      ((PDE.smoothPositivePartApprox_contDiff (k : ℝ) δ).differentiable
        (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt

private theorem shifted_gradient_error_decomposition
    (s a g D : ℝ) :
    s * a - D = s * (a - g) + (s * g - D) := by
  ring

private theorem tendsto_shifted_smooth_value
    {u : PDE.H1Function Ω} {φ : ℕ → PDE.Vec d → ℝ}
    (hφMeas : ∀ n, AEStronglyMeasurable (φ n) (PDE.volumeOn Ω))
    (hφ : Tendsto
      (fun n => eLpNorm (φ n - u.toFun) (2 : ℝ≥0∞) (PDE.volumeOn Ω))
      atTop (𝓝 0))
    (k : ℝ≥0) {δ : ℕ → ℝ}
    (hreg : Tendsto
      (fun n => eLpNorm
        (fun x => PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
          max (φ n x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm
        (fun x => PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
          max (u.toFun x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0) := by
  let reg : ℕ → PDE.Vec d → ℝ := fun n x =>
    PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
      max (φ n x - (k : ℝ)) 0
  let lip : ℕ → PDE.Vec d → ℝ := fun n x =>
    max (φ n x - (k : ℝ)) 0 - max (u.toFun x - (k : ℝ)) 0
  have hlipMeas : ∀ n, AEStronglyMeasurable (lip n) (PDE.volumeOn Ω) := by
    intro n
    exact (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable (hφMeas n)).sub
      (((continuous_id.sub continuous_const).max continuous_const)
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
  have hlipBound : ∀ n,
      eLpNorm (lip n) (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤
        eLpNorm (φ n - u.toFun) (2 : ℝ≥0∞) (PDE.volumeOn Ω) := by
    intro n
    apply eLpNorm_mono_ae (hlipMeas n)
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simpa only [lip, Pi.sub_apply, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (φ n x - (k : ℝ))
        (u.toFun x - (k : ℝ)) 0
  have hlip : Tendsto
      (fun n => eLpNorm (lip n) (2 : ℝ≥0∞) (PDE.volumeOn Ω))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ
      (fun _ => zero_le') hlipBound
  have hregMeas : ∀ n, AEStronglyMeasurable (reg n) (PDE.volumeOn Ω) := by
    intro n
    exact ((PDE.smoothPositivePartApprox_contDiff (k : ℝ) (δ n)).continuous
      |>.comp_aestronglyMeasurable (hφMeas n)).sub
      (((continuous_id.sub continuous_const).max continuous_const)
        |>.comp_aestronglyMeasurable (hφMeas n))
  have hsum : Tendsto
      (fun n => eLpNorm (reg n) (2 : ℝ≥0∞) (PDE.volumeOn Ω) +
        eLpNorm (lip n) (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0) := by
    simpa only [zero_add] using hreg.add hlip
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le') (fun n => ?_)
  have hdecomp :
      (fun x => PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n x) -
        max (u.toFun x - (k : ℝ)) 0) = reg n + lip n := by
    funext x
    simp only [reg, lip, Pi.add_apply]
    ring
  rw [hdecomp]
  exact eLpNorm_add_le (by norm_num)

private theorem tendsto_shifted_smooth_gradient
    {φ : ℕ → PDE.Vec d → ℝ} (hφSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (k : ℝ≥0) {δ : ℕ → ℝ} {g D : PDE.Vec d → PDE.Vec d}
    (hfirstMeas : ∀ i n, AEStronglyMeasurable
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
        ((fderiv ℝ (φ n) x) (PDE.basisVec i) - g x i)) (PDE.volumeOn Ω))
    (hsecondMeas : ∀ i n, AEStronglyMeasurable
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
      (PDE.volumeOn Ω))
    (hfirst : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
        ((fderiv ℝ (φ n) x) (PDE.basisVec i) - g x i))
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0))
    (hsecond : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0)) :
    ∀ i, Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ
        (fun y => PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n y)) x)
          (PDE.basisVec i) - D x i)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0) := by
  intro i
  have hsum : Tendsto (fun n =>
      eLpNorm
        (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
          ((fderiv ℝ (φ n) x) (PDE.basisVec i) - g x i))
        (2 : ℝ≥0∞) (PDE.volumeOn Ω) +
      eLpNorm
        (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0) := by
    simpa only [zero_add] using (hfirst i).add (hsecond i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le') (fun n => ?_)
  let first : PDE.Vec d → ℝ := fun x =>
    PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) *
      ((fderiv ℝ (φ n) x) (PDE.basisVec i) - g x i)
  let second : PDE.Vec d → ℝ := fun x =>
    PDE.smoothPositivePartStep (k : ℝ) (δ n) (φ n x) * g x i - D x i
  have hdecomp :
      (fun x => (fderiv ℝ
        (fun y => PDE.smoothPositivePartApprox (k : ℝ) (δ n) (φ n y)) x)
          (PDE.basisVec i) - D x i) = first + second := by
    funext x
    rw [fderiv_shifted_smooth_comp_basisVec (hφSmooth n) k x i]
    simp only [first, second, Pi.add_apply]
    exact shifted_gradient_error_decomposition _ _ _ _
  rw [hdecomp]
  exact eLpNorm_add_le (by norm_num)

private theorem tendsto_shifted_step_mul_sub_indicator
    {f : ℕ → PDE.Vec d → ℝ} {f₀ : PDE.Vec d → ℝ}
    {g : PDE.Vec d → ℝ} {x : PDE.Vec d} (k : ℝ≥0)
    {δ : ℕ → ℝ} (hδPos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hf : Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hzero : f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n =>
      PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
        (if (k : ℝ) < f₀ x then g x else 0)) atTop (𝓝 0) := by
  rcases lt_trichotomy (f₀ x) (k : ℝ) with hlt | heq | hgt
  · have hevent : ∀ᶠ n in atTop, f n x < (f₀ x + (k : ℝ)) / 2 :=
      (tendsto_order.1 hf).2 _ (by linarith)
    have hstep : ∀ᶠ n in atTop,
        PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) = 0 := by
      filter_upwards [hevent] with n hn
      exact PDE.smoothPositivePartStep_eq_zero (hδPos n) (by
        linarith [(hδPos n).le])
    apply (tendsto_congr' (hstep.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [if_neg hlt.not_gt, hn, zero_mul, sub_zero]
  · have hg : g x = 0 := hzero heq
    have hfun : (fun n =>
        PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
          (if (k : ℝ) < f₀ x then g x else 0)) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [hg]
      split <;> simp
    rw [hfun]
    exact tendsto_const_nhds
  · have hfLarge : ∀ᶠ n in atTop, (f₀ x + (k : ℝ)) / 2 < f n x :=
      (tendsto_order.1 hf).1 _ (by linarith)
    have hδSmall : ∀ᶠ n in atTop, δ n < (f₀ x - (k : ℝ)) / 4 :=
      (tendsto_order.1 hδ).2 _ (by linarith)
    have hone : ∀ᶠ n in atTop,
        PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) = 1 := by
      filter_upwards [hfLarge, hδSmall] with n hn hdn
      exact PDE.smoothPositivePartStep_eq_one (hδPos n) (by linarith)
    apply (tendsto_congr' (hone.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [if_pos hgt, hn, one_mul, sub_self]

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
  have hBFinite : ∫⁻ x, B x ∂μ ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hboundMem).ne
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [enorm_zero, Function.comp_def] using (continuous_enorm.tendsto 0).comp hx
    simpa only [G, Function.comp_def, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' B hGMeas hGBound hBFinite hGZero
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _),
      G, Function.comp_def, ENNReal.toReal_ofNat, one_div,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp hint

private theorem tendsto_shifted_step_indicator_eLpNorm
    {f : ℕ → PDE.Vec d → ℝ} {f₀ g : PDE.Vec d → ℝ}
    (hfMeas : ∀ n, AEStronglyMeasurable (f n) (PDE.volumeOn Ω))
    (hf₀Meas : AEStronglyMeasurable f₀ (PDE.volumeOn Ω))
    (hgMem : MemLp g (2 : ℝ≥0∞) (PDE.volumeOn Ω))
    (k : ℝ≥0) {δ : ℕ → ℝ} (hδPos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ᵐ x ∂(PDE.volumeOn Ω),
      Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hlevel : ∀ᵐ x ∂(PDE.volumeOn Ω), f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x -
        {y | (k : ℝ) < f₀ y}.indicator g x)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_zero_of_ae_dominated
    (bound := fun x => (2 : ℝ) * g x)
  · intro n
    apply AEStronglyMeasurable.sub
    · exact ((PDE.smoothPositivePartStep_continuous (k : ℝ) (δ n))
        |>.comp_aestronglyMeasurable (hfMeas n)).mul hgMem.aestronglyMeasurable
    · rw [aestronglyMeasurable_indicator_iff₀
      (nullMeasurableSet_lt aemeasurable_const hf₀Meas.aemeasurable)]
      exact hgMem.aestronglyMeasurable.restrict
  · exact hgMem.const_mul 2
  · intro n
    filter_upwards with x
    simp only [indicator_apply, Real.norm_eq_abs, norm_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    split_ifs
    · have hmul :
          |PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x| ≤ |g x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (PDE.abs_smoothPositivePartStep_le_one _ _ _)
      calc
        |PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x - g x| ≤
            |PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x) * g x| + |g x| :=
          abs_sub _ _
        _ ≤ |g x| + |g x| := add_le_add hmul le_rfl
        _ = 2 * |g x| := by ring
    · rw [sub_zero, abs_mul]
      calc
        |PDE.smoothPositivePartStep (k : ℝ) (δ n) (f n x)| * |g x| ≤ |g x| :=
          mul_le_of_le_one_left (abs_nonneg _) (PDE.abs_smoothPositivePartStep_le_one _ _ _)
        _ ≤ 2 * |g x| := by nlinarith [abs_nonneg (g x)]
  · filter_upwards [hf, hlevel] with x hfx hlx
    simpa only [indicator_apply, Set.mem_setOf_eq] using
      tendsto_shifted_step_mul_sub_indicator k hδPos hδ hfx hlx

private theorem exists_shiftedPositivePart_data
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ∃ v : H10HilbertGraph hΩ,
      valueCLM hΩ v = shiftedPositivePartValue k (valueCLM hΩ u) ∧
      ∀ᵐ x ∂(PDE.volumeOn Ω),
        gradientCLM hΩ v x =
          {y | (k : ℝ) < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  let w := h1FunctionOfH10 hΩ u
  let happrox := Classical.choice (h1FunctionOfH10_hasSupportedSmoothApproximation hΩ u)
  have happroxMeas : ∀ n,
      AEStronglyMeasurable (happrox.approx n) (PDE.volumeOn Ω) := by
    intro n
    exact (happrox.toWeakTestFunction n).memLp_toFun
      (2 : ℝ≥0∞) |>.aestronglyMeasurable
  obtain ⟨σ, hσStrictMono, hσAeRaw⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      happrox.tendsto_value).exists_seq_tendsto_ae
  have hσAe : ∀ᵐ x ∂(PDE.volumeOn Ω),
      Tendsto (fun n => happrox.approx (σ n) x) atTop (nhds (w.toFun x)) := by
    simpa only [PDE.H1Function.toW1pFunction_toFun] using hσAeRaw
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hεPos : ∀ n, 0 < ε n := by
    intro n
    dsimp only [ε]
    positivity
  have hεTendsto : Tendsto ε atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscale : ∀ n, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε n ∧
      eLpNorm
        (fun x => PDE.smoothPositivePartApprox (k : ℝ) δ
            (happrox.approx (σ n) x) -
          max (happrox.approx (σ n) x - (k : ℝ)) 0)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤ ENNReal.ofReal (ε n) := by
    intro n
    exact exists_shifted_regularization_scale
      (happrox.approx (σ n))
      (happrox.approx_hasCompactSupport (σ n)) (happroxMeas (σ n)) k (ε n) (hεPos n)
  let δ : ℕ → ℝ := fun n => Classical.choose (hscale n)
  have hδPos : ∀ n, 0 < δ n := fun n => (Classical.choose_spec (hscale n)).1
  have hδLe : ∀ n, δ n ≤ ε n := fun n => (Classical.choose_spec (hscale n)).2.1
  have hδTendsto : Tendsto δ atTop (nhds 0) :=
    squeeze_zero (fun n => (hδPos n).le) hδLe hεTendsto
  let shiftedApprox : ℕ → PDE.Vec d → ℝ := fun n x =>
    PDE.smoothPositivePartApprox (k : ℝ) (δ n) (happrox.approx (σ n) x)
  have hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (shiftedApprox n) := by
    intro n
    exact (PDE.smoothPositivePartApprox_contDiff (k : ℝ) (δ n)).comp
      (happrox.approx_smooth (σ n))
  have hcompact : ∀ n, HasCompactSupport (shiftedApprox n) := by
    intro n
    change HasCompactSupport
      ((fun s => PDE.smoothPositivePartApprox (k : ℝ) (δ n) s) ∘
        happrox.approx (σ n))
    have hzero : PDE.smoothPositivePartApprox (k : ℝ) (δ n) 0 = 0 :=
      PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2
    exact @HasCompactSupport.comp_left _ ℝ ℝ _ _ _ _ _
      (happrox.approx_hasCompactSupport (σ n)) hzero
  have hsupport : ∀ n, tsupport (shiftedApprox n) ⊆ Ω := by
    intro n
    refine (closure_mono (Function.support_comp_subset
      (PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) k.2)
      (happrox.approx (σ n)))).trans ?_
    exact happrox.approx_tsupport_subset (σ n)
  have hreg : Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartApprox (k : ℝ) (δ n)
          (happrox.approx (σ n) x) -
        max (happrox.approx (σ n) x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (nhds 0) from ?_)
      (fun _ => zero_le') (fun n => (Classical.choose_spec (hscale n)).2.2)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hεTendsto
  have hvalue : Tendsto (fun n => eLpNorm
      (fun x => shiftedApprox n x - max (w.toFun x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    apply tendsto_shifted_smooth_value
      (fun n => happroxMeas (σ n))
      (happrox.tendsto_value.comp hσStrictMono.tendsto_atTop) k
    simpa only [shiftedApprox] using hreg
  let g : PDE.Vec d → PDE.Vec d := fun x => (gradientCLM hΩ u x).ofLp
  let D : PDE.Vec d → PDE.Vec d := fun x =>
    {y | (k : ℝ) < w.toFun y}.indicator g x
  have hDCoord : ∀ x i, D x i =
      {y | (k : ℝ) < w.toFun y}.indicator (fun y => g y i) x := by
    intro x i
    simp only [D, indicator_apply]
    split <;> rfl
  have hgMem : PDE.GradMemL2On Ω g := w.gradMemL2
  have hDMem : PDE.GradMemL2On Ω D := by
    intro i
    rw [show (fun x => D x i) =
        {y | (k : ℝ) < w.toFun y}.indicator (fun y => g y i) by
      funext x; exact hDCoord x i]
    refine MemLp.of_le (hgMem i) ?_ ?_
    · exact (hgMem i).aestronglyMeasurable.indicator₀
        (nullMeasurableSet_lt aemeasurable_const
          w.memL2.aestronglyMeasurable.aemeasurable)
    · filter_upwards with x
      simp only [indicator_apply]
      split <;> simp
  have hfirstMeas : ∀ i n, AEStronglyMeasurable
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (PDE.basisVec i) - g x i))
      (PDE.volumeOn Ω) := by
    intro i n
    exact ((PDE.smoothPositivePartStep_continuous (k : ℝ) (δ n))
      |>.comp_aestronglyMeasurable (happroxMeas (σ n))).mul
      (((happrox.toWeakTestFunction (σ n)).memLp_partialDeriv i 2).aestronglyMeasurable.sub
        (hgMem i).aestronglyMeasurable)
  have hfirst : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (PDE.basisVec i) - g x i))
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (happrox.tendsto_grad i |>.comp hσStrictMono.tendsto_atTop)
      (fun _ => zero_le') (fun n => ?_)
    apply eLpNorm_mono_ae (hfirstMeas i n)
    filter_upwards with x
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (PDE.abs_smoothPositivePartStep_le_one _ _ _)
  have hsecondMeas : ∀ i n, AEStronglyMeasurable
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) * g x i - D x i) (PDE.volumeOn Ω) := by
    intro i n
    exact (((PDE.smoothPositivePartStep_continuous (k : ℝ) (δ n))
      |>.comp_aestronglyMeasurable (happroxMeas (σ n))).mul
      (hgMem i).aestronglyMeasurable).sub (hDMem i).aestronglyMeasurable
  have hlevel : ∀ᵐ x ∂(PDE.volumeOn Ω), w.toFun x = (k : ℝ) → g x = 0 := by
    filter_upwards [gradientCLM_ae_zero_on_level_set hΩ u (k : ℝ)] with x hx
    intro hval
    change (gradientCLM hΩ u x).ofLp = 0
    rw [hx hval]
    rfl
  have hsecond : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => PDE.smoothPositivePartStep (k : ℝ) (δ n)
        (happrox.approx (σ n) x) * g x i - D x i)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    intro i
    have ht := tendsto_shifted_step_indicator_eLpNorm
      (fun n => happroxMeas (σ n)) w.memL2.aestronglyMeasurable
      (hgMem i) k hδPos hδTendsto hσAe
      (by
        filter_upwards [hlevel] with x hx
        intro hval
        rw [hx hval]
        rfl)
    simpa only [hDCoord] using ht
  have hgrad : ∀ i, Tendsto (fun n => eLpNorm
      (fun x => (fderiv ℝ (shiftedApprox n) x) (PDE.basisVec i) - D x i)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
    simpa only [shiftedApprox] using tendsto_shifted_smooth_gradient
      (fun n => happrox.approx_smooth (σ n)) k hfirstMeas hsecondMeas hfirst hsecond
  have hfMem : PDE.MemL2On Ω (fun x => max (w.toFun x - (k : ℝ)) 0) :=
    memLp_max_sub_nonneg w.memL2 k
  have hweak : PDE.HasWeakGradientOn Ω
      (fun x => max (w.toFun x - (k : ℝ)) 0) D :=
    hasWeakGradientOn_of_smooth_approximation hfMem hDMem hsmooth hcompact hsupport
      (by simpa only [shiftedApprox, Pi.sub_def] using hvalue) hgrad
  let z : PDE.H1Function Ω :=
    { toFun := fun x => max (w.toFun x - (k : ℝ)) 0
      grad := D
      memL2 := hfMem
      gradMemL2 := hDMem
      hasWeakGradient := hweak }
  have hzApprox : Nonempty z.SupportedSmoothApproximation := ⟨
    { approx := shiftedApprox
      approx_smooth := hsmooth
      approx_hasCompactSupport := hcompact
      approx_tsupport_subset := hsupport
      tendsto_value := by simpa only [z, PDE.H1Function.toW1pFunction, Pi.sub_def] using hvalue
      tendsto_grad := by simpa only [z, PDE.H1Function.toW1pFunction] using hgrad }⟩
  let zg : PDE.H10Graph hΩ :=
    ⟨z.toW1pFunction.toW1pGraph,
      z.mem_h10Graph_of_supportedSmoothApproximation hΩ (Classical.choice hzApprox)⟩
  let v := (h10HilbertGraphContinuousLinearEquiv hΩ).symm zg
  refine ⟨v, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_fst z.toW1pFunction,
      coeFn_shiftedPositivePartValue k (valueCLM hΩ u)] with x hx hs
    change (zg : PDE.H1Graph Ω).1.1 x = shiftedPositivePartValue k (valueCLM hΩ u) x
    rw [hx, hs]
    rfl
  · filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_snd z.toW1pFunction] with x hx
    change (zg : PDE.H1Graph Ω).1.2 x = _
    rw [hx]
    ext i
    change z.grad x i = _
    change D x i = _
    rw [hDCoord]
    simp only [indicator_apply, w, h1FunctionOfH10, g]
    split <;> rfl

/-- The shifted positive part has a unique spatial `H¹₀` graph representative. -/
theorem exists_unique_h10ShiftedPositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ∃! v : H10HilbertGraph hΩ,
      valueCLM hΩ v = shiftedPositivePartValue k (valueCLM hΩ u) := by
  obtain ⟨v, hv, _⟩ := exists_shiftedPositivePart_data hΩ u k
  exact ⟨v, hv, fun z hz => valueCLM_injective hΩ (hz.trans hv.symm)⟩

/-- The canonical shifted positive part `(u - k)₊` in spatial `H¹₀`. -/
noncomputable def h10ShiftedPositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) : H10HilbertGraph hΩ :=
  Classical.choose (exists_unique_h10ShiftedPositivePart hΩ u k)

/-- The value component of the canonical shifted positive part. -/
@[simp]
theorem valueCLM_h10ShiftedPositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    valueCLM hΩ (h10ShiftedPositivePart hΩ u k) =
      shiftedPositivePartValue k (valueCLM hΩ u) :=
  (Classical.choose_spec (exists_unique_h10ShiftedPositivePart hΩ u k)).1

/-- Evaluation of the value representative of the shifted positive part. -/
theorem coeFn_valueCLM_h10ShiftedPositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    valueCLM hΩ (h10ShiftedPositivePart hΩ u k) =ᵐ[PDE.volumeOn Ω]
      fun x => max (valueCLM hΩ u x - (k : ℝ)) 0 := by
  rw [valueCLM_h10ShiftedPositivePart]
  exact coeFn_shiftedPositivePartValue k (valueCLM hΩ u)

/-- The weak gradient of `(u - k)₊` is the original gradient precisely on
the strict superlevel set `{k < u}` and is zero elsewhere. -/
theorem gradientCLM_h10ShiftedPositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ∀ᵐ x ∂(PDE.volumeOn Ω),
      gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) x =
        {y | (k : ℝ) < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  obtain ⟨v, hv, hvGrad⟩ := exists_shiftedPositivePart_data hΩ u k
  have heq : h10ShiftedPositivePart hΩ u k = v :=
    valueCLM_injective hΩ (valueCLM_h10ShiftedPositivePart hΩ u k |>.trans hv.symm)
  simpa only [heq] using hvGrad

/-- Shifted positive-part truncation contracts the value `L²` norm. -/
theorem norm_valueCLM_h10ShiftedPositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ‖valueCLM hΩ (h10ShiftedPositivePart hΩ u k)‖ ≤ ‖valueCLM hΩ u‖ := by
  rw [valueCLM_h10ShiftedPositivePart]
  exact norm_shiftedPositivePartValue_le k (valueCLM hΩ u)

/-- Shifted positive-part truncation contracts the weak-gradient `L²` norm. -/
theorem norm_gradientCLM_h10ShiftedPositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)‖ ≤ ‖gradientCLM hΩ u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  calc
    eLpNorm (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)) 2
        (PDE.volumeOn Ω) =
      eLpNorm ({y | (k : ℝ) < valueCLM hΩ u y}.indicator
        (gradientCLM hΩ u)) 2 (PDE.volumeOn Ω) :=
      eLpNorm_congr_ae (gradientCLM_h10ShiftedPositivePart hΩ u k)
    _ ≤ eLpNorm (gradientCLM hΩ u) 2 (PDE.volumeOn Ω) :=
      eLpNorm_mono_ae
        ((Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.indicator₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable.aemeasurable))
        (Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ x))

/-- Shifted positive-part truncation contracts the full spatial `H¹₀`
graph norm, with sharp constant one. -/
theorem norm_h10ShiftedPositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    ‖h10ShiftedPositivePart hΩ u k‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_h10HilbertGraph hΩ, norm_sq_h10HilbertGraph hΩ]
  exact add_le_add
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_valueCLM_h10ShiftedPositivePart_le hΩ u k))
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_gradientCLM_h10ShiftedPositivePart_le hΩ u k))

private theorem tendsto_shifted_value_threshold_eLpNorm
    {f : PDE.Vec d → ℝ} (hf : MemLp f (2 : ℝ≥0∞) (PDE.volumeOn Ω))
    {kn : ℕ → ℝ≥0} {k : ℝ≥0} (hk : Tendsto kn atTop (nhds k)) :
    Tendsto (fun n => eLpNorm
      (fun x => max (f x - (kn n : ℝ)) 0 - max (f x - (k : ℝ)) 0)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) atTop (nhds 0) := by
  apply tendsto_eLpNorm_two_zero_of_ae_dominated
    (bound := fun x => (2 : ℝ) * f x)
  · intro n
    exact (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub
      (((continuous_id.sub continuous_const).max continuous_const)
        |>.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · exact hf.const_mul 2
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hnonneg (a : ℝ≥0) : 0 ≤ max (f x - (a : ℝ)) 0 := le_max_right _ _
    have hle (a : ℝ≥0) : max (f x - (a : ℝ)) 0 ≤ |f x| := by
      rcases le_total (f x) (a : ℝ) with h | h
      · rw [max_eq_right (sub_nonpos.mpr h)]
        exact abs_nonneg _
      · rw [max_eq_left (sub_nonneg.mpr h), abs_of_nonneg (a.2.trans h)]
        exact sub_le_self _ a.2
    calc
      |max (f x - (kn n : ℝ)) 0 - max (f x - (k : ℝ)) 0| ≤
          max (f x - (kn n : ℝ)) 0 + max (f x - (k : ℝ)) 0 :=
        abs_sub_le_iff.2 ⟨by linarith [hnonneg k], by linarith [hnonneg (kn n)]⟩
      _ ≤ |f x| + |f x| := add_le_add (hle (kn n)) (hle k)
      _ = 2 * |f x| := by ring
  · filter_upwards with x
    have hkr : Tendsto (fun n => (kn n : ℝ)) atTop (nhds (k : ℝ)) :=
      continuous_subtype_val.tendsto k |>.comp hk
    have hm : Tendsto (fun a : ℝ => max (f x - a) 0) (nhds (k : ℝ))
        (nhds (max (f x - (k : ℝ)) 0)) :=
      ((show Continuous (fun a : ℝ => max (f x - a) 0) from
        (continuous_const.sub continuous_id).max continuous_const).tendsto _)
    have hc : Tendsto (fun _ : ℕ => max (f x - (k : ℝ)) 0) atTop
        (nhds (max (f x - (k : ℝ)) 0)) := tendsto_const_nhds
    simpa only [Function.comp_def, sub_self] using (hm.comp hkr).sub hc

private theorem tendsto_moving_indicator_sub_indicator
    {f : ℕ → PDE.Vec d → ℝ} {f₀ : PDE.Vec d → ℝ}
    {kn : ℕ → ℝ≥0} {k : ℝ≥0} {g : PDE.Vec d → WithLp 2 (PDE.Vec d)}
    {x : PDE.Vec d} (hf : Tendsto (fun n => f n x) atTop (nhds (f₀ x)))
    (hk : Tendsto kn atTop (nhds k)) (hzero : f₀ x = (k : ℝ) → g x = 0) :
    Tendsto (fun n =>
      {y | (kn n : ℝ) < f n y}.indicator g x -
        {y | (k : ℝ) < f₀ y}.indicator g x) atTop (nhds 0) := by
  have hdiff : Tendsto (fun n => f n x - (kn n : ℝ)) atTop
      (nhds (f₀ x - (k : ℝ))) :=
    hf.sub (continuous_subtype_val.tendsto k |>.comp hk)
  rcases lt_trichotomy (f₀ x) (k : ℝ) with hlt | heq | hgt
  · have hevent : ∀ᶠ n in atTop, f n x - (kn n : ℝ) < 0 :=
      (tendsto_order.1 hdiff).2 _ (sub_neg.mpr hlt)
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, not_lt.mpr (sub_nonpos.mp hn.le),
      hlt.not_gt, sub_self]
  · have hg : g x = 0 := hzero heq
    have hfun : (fun n =>
        {y | (kn n : ℝ) < f n y}.indicator g x -
          {y | (k : ℝ) < f₀ y}.indicator g x) =
        fun _ : ℕ => (0 : WithLp 2 (PDE.Vec d)) := by
      funext n
      simp only [indicator_apply, hg]
      split <;> split <;> simp
    rw [hfun]
    exact tendsto_const_nhds
  · have hevent : ∀ᶠ n in atTop, 0 < f n x - (kn n : ℝ) :=
      (tendsto_order.1 hdiff).1 _ (sub_pos.mpr hgt)
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, sub_pos.mp hn, hgt, sub_self]

private theorem indicator_sub_add_indicator_difference
    {E : Type*} [AddCommGroup E] {A B : Set (PDE.Vec d)}
    (a b : PDE.Vec d → E) (x : PDE.Vec d) :
    A.indicator (a - b) x + (A.indicator b x - B.indicator b x) =
      A.indicator a x - B.indicator b x := by
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    simp [hxA, hxB]

private theorem tendsto_h10_of_value_gradient
    (hΩ : IsOpen Ω) {un : ℕ → H10HilbertGraph hΩ} {u : H10HilbertGraph hΩ}
    (hv : Tendsto (fun n => valueCLM hΩ (un n)) atTop (nhds (valueCLM hΩ u)))
    (hg : Tendsto (fun n => gradientCLM hΩ (un n)) atTop
      (nhds (gradientCLM hΩ u))) : Tendsto un atTop (nhds u) := by
  rw [Metric.tendsto_atTop] at hv hg ⊢
  intro ε hε
  obtain ⟨Nv, hNv⟩ := hv (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  obtain ⟨Ng, hNg⟩ := hg (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨max Nv Ng, fun n hn => ?_⟩
  have hvn := hNv n (le_trans (le_max_left _ _) hn)
  have hgn := hNg n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm]
  change ‖un n - u‖ < ε
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).1
  rw [norm_sq_h10HilbertGraph hΩ]
  simp only [map_sub]
  rw [dist_eq_norm] at hvn hgn
  have hv2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hvn
  have hg2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hgn
  rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at hv2 hg2
  linarith

/-- The shifted positive part is jointly strongly continuous in the spatial
`H¹₀` function and the nonnegative threshold. -/
theorem continuous_h10ShiftedPositivePart (hΩ : IsOpen Ω) :
    Continuous (fun p : H10HilbertGraph hΩ × ℝ≥0 =>
      h10ShiftedPositivePart hΩ p.1 p.2) := by
  rw [continuous_iff_seqContinuous]
  rintro pn ⟨u, k⟩ hpn
  have hu : Tendsto (fun n => (pn n).1) atTop (nhds u) :=
    (continuous_fst.tendsto (u, k)).comp hpn
  have hk : Tendsto (fun n => (pn n).2) atTop (nhds k) :=
    (continuous_snd.tendsto (u, k)).comp hpn
  have huValue : Tendsto (fun n => valueCLM hΩ (pn n).1)
      atTop (nhds (valueCLM hΩ u)) := ((valueCLM hΩ).continuous.tendsto u).comp hu
  have huGrad : Tendsto (fun n => gradientCLM hΩ (pn n).1)
      atTop (nhds (gradientCLM hΩ u)) := ((gradientCLM hΩ).continuous.tendsto u).comp hu
  let μ := PDE.volumeOn Ω
  let f : ℕ → PDE.Vec d → ℝ := fun n => valueCLM hΩ (pn n).1
  let f₀ : PDE.Vec d → ℝ := valueCLM hΩ u
  let g : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) :=
    fun n => gradientCLM hΩ (pn n).1
  let g₀ : PDE.Vec d → WithLp 2 (PDE.Vec d) := gradientCLM hΩ u
  have hvalue : Tendsto
      (fun n => valueCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2))
      atTop (nhds (valueCLM hΩ (h10ShiftedPositivePart hΩ u k))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfun : Tendsto (fun n => eLpNorm
        (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - ((pn n).2 : ℝ)) 0) 2 μ) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'
          (fun n => valueCLM hΩ (pn n).1) (valueCLM hΩ u)).1 huValue)
        (fun _ => zero_le') (fun n => ?_)
      apply eLpNorm_mono_ae
        ((((continuous_id.sub continuous_const).max continuous_const)
          |>.comp_aestronglyMeasurable (Lp.memLp (valueCLM hΩ (pn n).1)).aestronglyMeasurable).sub
          (((continuous_id.sub continuous_const).max continuous_const)
            |>.comp_aestronglyMeasurable (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable))
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simpa only [f, f₀, Pi.sub_apply, id_eq, sub_sub_sub_cancel_right] using
        abs_max_sub_max_le_abs (f n x - ((pn n).2 : ℝ))
          (f₀ x - ((pn n).2 : ℝ)) 0
    have hthreshold := tendsto_shifted_value_threshold_eLpNorm
      (Lp.memLp (valueCLM hΩ u)) hk
    have hsum := hfun.add hthreshold
    have hraw : Tendsto (fun n => eLpNorm
        (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - (k : ℝ)) 0) 2 μ) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hsum) (fun _ => zero_le') (fun n => ?_)
      have hdecomp : (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
          max (f₀ x - (k : ℝ)) 0) =
          (fun x => max (f n x - ((pn n).2 : ℝ)) 0 -
            max (f₀ x - ((pn n).2 : ℝ)) 0) +
          (fun x => max (f₀ x - ((pn n).2 : ℝ)) 0 -
            max (f₀ x - (k : ℝ)) 0) := by
        funext x
        simp only [Pi.add_apply]
        ring
      rw [hdecomp]
      exact eLpNorm_add_le (by norm_num)
    refine hraw.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [coeFn_valueCLM_h10ShiftedPositivePart hΩ (pn n).1 (pn n).2,
        coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with x hnx hx
    rw [Pi.sub_apply, hnx, hx]
  let R : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) := fun n x =>
    {y | ((pn n).2 : ℝ) < f n y}.indicator g₀ x -
      {y | (k : ℝ) < f₀ y}.indicator g₀ x
  have hR : Tendsto (fun n => eLpNorm (R n) 2 μ) atTop (nhds 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms, hae⟩ :=
      (tendstoInMeasure_of_tendsto_Lp (huValue.comp hns)).exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := g₀)
    · intro n
      apply AEStronglyMeasurable.sub
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ (pn (ns (ms n))).1)).aestronglyMeasurable.aemeasurable)]
        exact (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.restrict
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.memLp (valueCLM hΩ u)).aestronglyMeasurable.aemeasurable)]
        exact (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable.restrict
    · exact Lp.memLp (gradientCLM hΩ u)
    · intro n
      filter_upwards with x
      simp only [R, g₀, indicator_apply]
      split <;> split <;> simp
    · filter_upwards [hae, gradientCLM_ae_zero_on_level_set hΩ u (k : ℝ)] with x hx hz
      exact tendsto_moving_indicator_sub_indicator hx
        (hk.comp (hns.comp hms.tendsto_atTop)) hz
  have hgrad : Tendsto
      (fun n => gradientCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2))
      atTop (nhds (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) := by
    let q : ℕ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := fun n =>
      gradientCLM hΩ (h10ShiftedPositivePart hΩ (pn n).1 (pn n).2)
    let q₀ : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      gradientCLM hΩ (h10ShiftedPositivePart hΩ u k)
    change Tendsto q atTop (nhds q₀)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfirst : Tendsto (fun n => eLpNorm
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀)) 2 μ)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 huGrad)
        (fun _ => zero_le') (fun n => eLpNorm_mono_ae
          (((Lp.memLp (gradientCLM hΩ (pn n).1)).aestronglyMeasurable.sub
            (Lp.memLp (gradientCLM hΩ u)).aestronglyMeasurable).indicator₀
            (nullMeasurableSet_lt aemeasurable_const
              (Lp.memLp (valueCLM hΩ (pn n).1)).aestronglyMeasurable.aemeasurable))
          (Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ x)))
    have hraw : Tendsto (fun n => eLpNorm
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) 2 μ)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hfirst.add hR) (fun _ => zero_le') (fun n => ?_)
      exact eLpNorm_add_le (by norm_num)
    refine hraw.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [gradientCLM_h10ShiftedPositivePart hΩ (pn n).1 (pn n).2,
        gradientCLM_h10ShiftedPositivePart hΩ u k] with x hnx hx
    have hpoint :
        ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) x =
          q n x - q₀ x := by
      calc
      ({y | ((pn n).2 : ℝ) < f n y}.indicator (g n - g₀) + R n) x =
          {y | ((pn n).2 : ℝ) < f n y}.indicator (g n) x -
            {y | (k : ℝ) < f₀ y}.indicator g₀ x := by
          rw [Pi.add_apply]
          exact indicator_sub_add_indicator_difference (g n) g₀ x
      _ = q n x - q₀ x := by
          dsimp only [f, f₀, g, g₀, q, q₀]
          exact congrArg₂ (fun a b : WithLp 2 (PDE.Vec d) => a - b)
            hnx.symm hx.symm
    simpa only [Pi.sub_apply] using hpoint
  exact tendsto_h10_of_value_gradient hΩ hvalue hgrad

end HypoellipticAleksandrov.Parabolic.Dirichlet
