module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Prod

/-!
Finite-range raw representatives for the product of two `L²` spaces.

This module deliberately treats the quotient-valued inner `Lp` functions only
through their canonical cofunctions and almost-everywhere identities.
-/

@[expose] public section

open scoped ENNReal MeasureTheory

namespace HypoellipticAleksandrov

open MeasureTheory

noncomputable section

/-- The raw product representative obtained from a finite-range outer simple function. -/
noncomputable def simpleUncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) : α × β → ℝ :=
  fun z => s z.1 z.2

/-- A finite-range outer `L²` function has a jointly strongly measurable raw lift. -/
theorem stronglyMeasurable_simpleUncurry
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) :
    StronglyMeasurable (simpleUncurry s) := by
  classical
  refine SimpleFunc.induction' (P := fun s => StronglyMeasurable (simpleUncurry s)) ?_ ?_ s
  · intro c
    exact (MeasureTheory.Lp.stronglyMeasurable c).comp_measurable measurable_snd
  · intro f g t ht hf hg
    let : DecidablePred fun z : α × β => z ∈ t ×ˢ Set.univ := Classical.decPred _
    convert StronglyMeasurable.piecewise (MeasurableSet.prod ht MeasurableSet.univ) hf hg using 1
    · ext z
      by_cases hz : z.1 ∈ t <;> simp [simpleUncurry, hz]
    · exact Classical.decPred _

/-- The raw lift agrees with the canonical inner cofunction on every outer slice. -/
theorem ae_slice_simpleUncurry
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {ν : Measure β}
    (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) :
    ∀ᵐ x ∂μ, (fun y => simpleUncurry s (x, y)) =ᵐ[ν] fun y => s x y := by
  filter_upwards with x
  filter_upwards with y
  rfl

private theorem integral_sq_coeFn_eq_norm_sq
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    (c : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν) :
    ∫ y, c y ^ 2 ∂ν = ‖c‖ ^ 2 := by
  calc
    ∫ y, c y ^ 2 ∂ν = ∫ y, inner ℝ (c y) (c y) ∂ν := by
      congr with y
      simp [pow_two]
    _ = inner ℝ c c := (MeasureTheory.L2.inner_def c c).symm
    _ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c

/-- The raw lift of an outer simple `L²` function belongs to product `L²`. -/
theorem memLp_simpleUncurry_two
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ) :
    MeasureTheory.MemLp (simpleUncurry s) (2 : ℝ≥0∞) (μ.prod ν) := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq
    (stronglyMeasurable_simpleUncurry s).aestronglyMeasurable]
  change Integrable (fun z : α × β => simpleUncurry s z ^ 2) (μ.prod ν)
  refine (MeasureTheory.integrable_prod_iff ?_).2 ?_
  · exact
      ((stronglyMeasurable_simpleUncurry s).pow 2).aestronglyMeasurable
  constructor
  · filter_upwards with x
    simpa [simpleUncurry] using (MeasureTheory.Lp.memLp (s x)).integrable_sq
  · have houter : Integrable (fun x => ‖s x‖ ^ 2) μ :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
    refine houter.congr ?_
    filter_upwards with x
    change ‖s x‖ ^ 2 = ∫ y, ‖s x y ^ 2‖ ∂ν
    symm
    calc
      (∫ y, ‖s x y ^ 2‖ ∂ν) = ∫ y, s x y ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg (s x y))
      _ = ‖s x‖ ^ 2 := integral_sq_coeFn_eq_norm_sq ν (s x)

/-- Subtraction of raw lifts agrees almost everywhere with the raw lift of subtraction. -/
theorem ae_simpleUncurry_sub
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s t : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν)) :
    simpleUncurry (s - t) =ᵐ[μ.prod ν] simpleUncurry s - simpleUncurry t := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
    ((stronglyMeasurable_simpleUncurry (s - t)).measurableSet_eq_fun
      ((stronglyMeasurable_simpleUncurry s).sub (stronglyMeasurable_simpleUncurry t)))).2
  filter_upwards with x
  filter_upwards [MeasureTheory.Lp.coeFn_sub (s x) (t x)] with y hy
  exact hy

/-- The `L²` norm of the product lift equals the outer `L²` norm. -/
theorem norm_simpleUncurry_toLp_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ) :
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s)‖ = ‖hs.toLp s‖ := by
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  apply congrArg ENNReal.toReal
  apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
  calc
    MeasureTheory.eLpNorm (simpleUncurry s) (2 : ℝ≥0∞) (μ.prod ν) ^ (2 : ℝ) =
        ∫⁻ z, ‖simpleUncurry s z‖ₑ ^ (2 : ℝ) ∂μ.prod ν := by
      simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
        (f := simpleUncurry s) (μ := μ.prod ν) (p := (2 : NNReal)) (by norm_num)
        (stronglyMeasurable_simpleUncurry s).aestronglyMeasurable)
    _ = ∫⁻ x, ∫⁻ y, ‖simpleUncurry s (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ :=
      MeasureTheory.lintegral_prod _
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (stronglyMeasurable_simpleUncurry s).enorm.aemeasurable)
    _ = ∫⁻ x, ‖s x‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      symm
      simpa [simpleUncurry, MeasureTheory.Lp.enorm_def] using
        (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
          (f := fun y => s x y) (μ := ν) (p := (2 : NNReal)) (by norm_num)
          (MeasureTheory.Lp.aestronglyMeasurable (s x)))
    _ = MeasureTheory.eLpNorm s (2 : ℝ≥0∞) μ ^ (2 : ℝ) := by
      simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
        (f := s) (μ := μ) (p := (2 : NNReal)) (by norm_num) hs.aestronglyMeasurable).symm

/-- The norm of the difference of two product lifts equals the outer difference norm. -/
theorem norm_sub_simpleUncurry_toLp_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (s t : SimpleFunc α (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ν))
    (hs : MeasureTheory.MemLp s (2 : ℝ≥0∞) μ)
    (ht : MeasureTheory.MemLp t (2 : ℝ≥0∞) μ) :
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t)‖ =
      ‖hs.toLp s - ht.toLp t‖ := by
  have hproduct_sub :
      (memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t) =
      (memLp_simpleUncurry_two μ ν (s - t) (hs.sub ht)).toLp (simpleUncurry (s - t)) := by
    rw [← MeasureTheory.MemLp.toLp_sub]
    apply MeasureTheory.MemLp.toLp_congr
    exact (ae_simpleUncurry_sub μ ν s t).symm
  calc
    ‖(memLp_simpleUncurry_two μ ν s hs).toLp (simpleUncurry s) -
        (memLp_simpleUncurry_two μ ν t ht).toLp (simpleUncurry t)‖ =
        ‖(memLp_simpleUncurry_two μ ν (s - t) (hs.sub ht)).toLp
          (simpleUncurry (s - t))‖ := by rw [hproduct_sub]
    _ = ‖(hs.sub ht).toLp (s - t)‖ :=
      norm_simpleUncurry_toLp_eq μ ν (s - t) (hs.sub ht)
    _ = ‖hs.toLp s - ht.toLp t‖ := by
      rw [← MeasureTheory.MemLp.toLp_sub]
      apply congrArg norm
      apply MeasureTheory.MemLp.toLp_congr
      filter_upwards with x
      rfl

end

end HypoellipticAleksandrov
