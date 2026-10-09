module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Convergence consequences of `L^p` convergence

This file provides measure-generic limit lemmas for extended-real `L^p`
seminorms.

## Main results

- `tendsto_eLpNorm_of_tendsto_sub`: convergence in `L^p` implies convergence
  of the `L^p` seminorms when the limiting seminorm is finite.
- `tendsto_integral_of_tendsto_eLpNorm_sub`: on a probability measure,
  `L^p` convergence for `p ≥ 1` implies convergence of Bochner integrals.
- `tendsto_average_of_tendsto_eLpNorm_sub`: the corresponding statement for
  Mathlib's average notation.

The integral results include the endpoint `p = 1`. They first compare the
`L^1` and `L^p` seminorms and then use continuity of the Bochner integral in
`L^1`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A sequence cannot converge in the same finite-exponent `Lᵖ` seminorm to
two different almost-everywhere classes. -/
theorem ae_eq_of_tendsto_eLpNorm_sub
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f g : α → E} {l : Filter ι}
    [NeBot l]
    (_hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (_hf : AEStronglyMeasurable f μ)
    (_hg : AEStronglyMeasurable g μ)
    (hFf :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0))
    (hFg :
      Tendsto
        (fun i => eLpNorm (F i - g) p μ)
        l (𝓝 0)) :
    f =ᵐ[μ] g := by
  have hbound :
      ∀ i,
        eLpNorm (f - g) p μ ≤
          eLpNorm (F i - f) p μ +
            eLpNorm (F i - g) p μ := by
    intro i
    have heq : f - g = (f - F i) + (F i - g) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    calc
      eLpNorm (f - g) p μ =
          eLpNorm ((f - F i) + (F i - g)) p μ :=
        congrArg (fun h => eLpNorm h p μ) heq
      _ ≤
          eLpNorm (f - F i) p μ +
            eLpNorm (F i - g) p μ :=
        eLpNorm_add_le
          hp
      _ =
          eLpNorm (F i - f) p μ +
            eLpNorm (F i - g) p μ := by
        rw [eLpNorm_sub_comm f (F i)]
  have hsum :
      Tendsto
        (fun i =>
          eLpNorm (F i - f) p μ +
            eLpNorm (F i - g) p μ)
        l (𝓝 0) := by
    simpa only [zero_add] using hFf.add hFg
  have hzero : eLpNorm (f - g) p μ = 0 := by
    apply le_antisymm
    · exact
        le_of_tendsto_of_tendsto'
          tendsto_const_nhds hsum hbound
    · exact bot_le
  have hpZero : p ≠ 0 := by
    exact ne_of_gt (zero_lt_one.trans_le hp)
  have hdiff :
      (fun x => f x - g x) =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff hpZero).mp hzero
  filter_upwards [hdiff] with x hx
  exact sub_eq_zero.mp hx

/-- The extended-real `L^p` seminorm is continuous along `L^p`-convergent
families when `p ≥ 1` and the limiting seminorm is finite. -/
theorem tendsto_eLpNorm_of_tendsto_sub
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f : α → E} {l : Filter ι}
    (_hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (_hf : AEStronglyMeasurable f μ)
    (hfin : eLpNorm f p μ ≠ ∞)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i => eLpNorm (F i) p μ)
      l (𝓝 (eLpNorm f p μ)) := by
  have hupper :
      ∀ i,
        eLpNorm (F i) p μ ≤
          eLpNorm f p μ + eLpNorm (F i - f) p μ := by
    intro i
    have heq : F i = f + (F i - f) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    calc
      eLpNorm (F i) p μ =
          eLpNorm (f + (F i - f)) p μ :=
        congrArg (fun g => eLpNorm g p μ) heq
      _ ≤
          eLpNorm f p μ + eLpNorm (F i - f) p μ :=
        eLpNorm_add_le hp
  have hlower :
      ∀ i,
        eLpNorm f p μ - eLpNorm (F i - f) p μ ≤
          eLpNorm (F i) p μ := by
    intro i
    rw [tsub_le_iff_right]
    calc
      eLpNorm f p μ =
          eLpNorm (F i + (f - F i)) p μ := by
        congr 1
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        abel
      _ ≤
          eLpNorm (F i) p μ +
            eLpNorm (f - F i) p μ :=
        eLpNorm_add_le hp
      _ =
          eLpNorm (F i) p μ +
            eLpNorm (F i - f) p μ := by
        rw [eLpNorm_sub_comm]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun i =>
        eLpNorm f p μ - eLpNorm (F i - f) p μ)
      (h := fun i =>
        eLpNorm f p μ + eLpNorm (F i - f) p μ)
      ?_ ?_ hlower hupper
  · have hlowerTendsto :=
      ENNReal.Tendsto.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ι => eLpNorm f p μ)
            l (𝓝 (eLpNorm f p μ)))
        h (Or.inl hfin)
    simpa using hlowerTendsto
  · have hupperTendsto :=
      Tendsto.const_add (eLpNorm f p μ) h
    simpa only [add_zero] using hupperTendsto

/-- On a probability measure, `L^p` convergence with `p ≥ 1` implies
convergence of Bochner integrals.

Only integrability of the limit and strong measurability of the approximants
are assumed. The `L^p` convergence itself makes the approximants integrable
eventually. -/
theorem tendsto_integral_of_tendsto_eLpNorm_sub
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f : α → E} {l : Filter ι}
    (_hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : Integrable f μ)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i => ∫ x, F i x ∂μ)
      l (𝓝 (∫ x, f x ∂μ)) := by
  have hFIntegrable :
      ∀ᶠ i in l, Integrable (F i) μ := by
    filter_upwards
      [(tendsto_order.1 h).2 1 zero_lt_one] with i hi
    have hdiffMemLp :
        MemLp (F i - f) p μ :=
      (hi.trans ENNReal.one_lt_top)
    have hdiffIntegrable :
        Integrable (F i - f) μ :=
      hdiffMemLp.integrable hp
    simpa only [sub_add_cancel] using
      hdiffIntegrable.add hf
  have hL1 :
      Tendsto
        (fun i => eLpNorm (F i - f) 1 μ)
        l (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds h
        (Eventually.of_forall fun _ => zero_le)
        ?_
    exact
      Eventually.of_forall fun i =>
        eLpNorm_le_eLpNorm_of_exponent_le hp
  exact
    tendsto_integral_of_L1'
      f hFIntegrable hL1

/-- On a probability measure, `L^p` convergence with `p ≥ 1` implies
convergence of averages. -/
theorem tendsto_average_of_tendsto_eLpNorm_sub
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ι → α → E} {f : α → E} {l : Filter ι}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : Integrable f μ)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i => ⨍ x, F i x ∂μ)
      l (𝓝 (⨍ x, f x ∂μ)) := by
  simpa only [average_eq_integral] using
    tendsto_integral_of_tendsto_eLpNorm_sub
      hp hF hf h

/-- On a probability measure, centering an `L^p`-convergent sequence by its
integral preserves `L^p` convergence. This includes the endpoint `p = 1`. -/
theorem tendsto_eLpNorm_centered_sub_zero
    {ι α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ι → α → ℝ} {f : α → ℝ} {l : Filter ι}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hf : Integrable f μ)
    (h :
      Tendsto
        (fun i => eLpNorm (F i - f) p μ)
        l (𝓝 0)) :
    Tendsto
      (fun i =>
        eLpNorm
          (fun x =>
            (F i x - ∫ y, F i y ∂μ) -
              (f x - ∫ y, f y ∂μ))
          p μ)
      l (𝓝 0) := by
  have hpZero : p ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hp)
  have hIntegral :=
    tendsto_integral_of_tendsto_eLpNorm_sub
      hp hF hf h
  have hIntegralDiff :
      Tendsto
        (fun i => (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
        l (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ι => ∫ y, f y ∂μ)
          l (𝓝 (∫ y, f y ∂μ)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hConst.sub hIntegral
  have hConstantNorm :
      Tendsto
        (fun i =>
          eLpNorm
            (fun _ : α =>
              (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
            p μ)
        l (𝓝 0) := by
    have hEnorm :
        Tendsto
          (fun i =>
            ‖(∫ y, f y ∂μ) - ∫ y, F i y ∂μ‖ₑ)
          l (𝓝 0) := by
      simpa only [enorm_zero] using hIntegralDiff.enorm
    have hFormula :
        (fun i =>
          eLpNorm
            (fun _ : α =>
              (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
            p μ) =
          fun i =>
            ‖(∫ y, f y ∂μ) - ∫ y, F i y ∂μ‖ₑ := by
      funext i
      rw [eLpNorm_const'
        ((∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
        hpZero hpTop]
      simp only [measure_univ, ENNReal.one_rpow, mul_one]
    rw [hFormula]
    exact hEnorm
  have hBound :
      ∀ i,
        eLpNorm
            (fun x =>
              (F i x - ∫ y, F i y ∂μ) -
                (f x - ∫ y, f y ∂μ))
            p μ ≤
          eLpNorm (F i - f) p μ +
            eLpNorm
              (fun _ : α =>
                (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
              p μ := by
    intro i
    let A : α → ℝ :=
      F i - f
    let B : α → ℝ :=
      fun _ =>
        (∫ y, f y ∂μ) - ∫ y, F i y ∂μ
    have hA :
        AEStronglyMeasurable A μ :=
      (hF i).sub hf.aestronglyMeasurable
    have hB :
        AEStronglyMeasurable B μ :=
      aestronglyMeasurable_const
    calc
      eLpNorm
          (fun x =>
            (F i x - ∫ y, F i y ∂μ) -
              (f x - ∫ y, f y ∂μ))
          p μ =
        eLpNorm (A + B) p μ := by
          apply eLpNorm_congr_ae
          filter_upwards with x
          dsimp only [A, B, Pi.sub_apply, Pi.add_apply]
          ring
      _ ≤ eLpNorm A p μ + eLpNorm B p μ :=
        eLpNorm_add_le hp
      _ =
          eLpNorm (F i - f) p μ +
            eLpNorm
              (fun _ : α =>
                (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
              p μ :=
        rfl
  have hUpper :
      Tendsto
        (fun i =>
          eLpNorm (F i - f) p μ +
            eLpNorm
              (fun _ : α =>
                (∫ y, f y ∂μ) - ∫ y, F i y ∂μ)
              p μ)
        l (𝓝 0) := by
    simpa only [zero_add] using h.add hConstantNorm
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun _ => zero_le) hBound

end PDE
