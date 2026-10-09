module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Zero extension of restricted-measure `Lp` functions

This module constructs the canonical quotient-level extension-by-zero map from
an `Lp` space over a measurable restricted measure to the ambient `Lp` space.
The map is specified only through the canonical `Lp` function coercion and an
ambient almost-everywhere indicator formula.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

/-- The quotient representative for extension by zero. -/
def zeroExtend
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : Lp E p (μ.restrict s)) :
    Lp E p μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
    (Set.indicator s (⇑f))

private theorem coeFn_zeroExtend
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : Lp E p (μ.restrict s)) :
    ⇑(zeroExtend hs f) =ᵐ[μ] Set.indicator s (⇑f) := by
  change ⇑(((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
    (Set.indicator s (⇑f))) =ᵐ[μ] Set.indicator s (⇑f)
  exact @MemLp.coeFn_toLp α E _ p μ _ (Set.indicator s (⇑f))
    ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f))

private theorem indicator_add_ae
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (f g : Lp E p (μ.restrict s)) :
    Set.indicator s (⇑(f + g)) =ᵐ[μ]
      Set.indicator s (⇑f) + Set.indicator s (⇑g) := by
  filter_upwards [ae_imp_of_ae_restrict (Lp.coeFn_add f g)] with x hfg
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, hfg hx, Pi.add_apply]
  · simp only [Pi.add_apply, Set.indicator_of_notMem hx, zero_add]

private theorem indicator_smul_ae
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (c : ℝ) (f : Lp E p (μ.restrict s)) :
    Set.indicator s (⇑(c • f)) =ᵐ[μ] c • Set.indicator s (⇑f) := by
  filter_upwards [ae_imp_of_ae_restrict (Lp.coeFn_smul c f)] with x hcf
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, hcf hx, Pi.smul_apply]
  · simp only [Pi.smul_apply, Set.indicator_of_notMem hx, smul_zero]

/-- Extension by zero from `Lp E p (μ.restrict s)` to `Lp E p μ`, as a
linear isometry. -/
noncomputable def zeroExtendLinearIsometry
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) :
    Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toFun f := zeroExtend hs f
  map_add' f g := by
    apply Lp.ext
    exact (coeFn_zeroExtend hs (f + g)).trans
      ((indicator_add_ae f g).trans (((coeFn_zeroExtend hs f).add
        (coeFn_zeroExtend hs g)).symm.trans
          (Lp.coeFn_add (zeroExtend hs f) (zeroExtend hs g)).symm))
  map_smul' c f := by
    apply Lp.ext
    have hsmul : c • Set.indicator s (⇑f) =ᵐ[μ] ⇑(c • zeroExtend hs f) := by
      filter_upwards [coeFn_zeroExtend hs f,
        Lp.coeFn_smul c (zeroExtend hs f)] with x hf hcf
      simp only [hf, hcf, Pi.smul_apply]
    exact (coeFn_zeroExtend hs (c • f)).trans
      ((indicator_smul_ae c f).trans hsmul)
  norm_map' f := by
    change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
      (Set.indicator s (⇑f))‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs,
      Lp.norm_def]

/-- The zero-extension is represented almost everywhere by the literal
indicator of the restricted-volume representative. -/
theorem coeFn_zeroExtendLinearIsometry
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : Lp E p (μ.restrict s)) :
    ⇑(zeroExtendLinearIsometry hs f) =ᵐ[μ]
      Set.indicator s (⇑f) :=
  coeFn_zeroExtend hs f

end MeasureTheory.Lp
