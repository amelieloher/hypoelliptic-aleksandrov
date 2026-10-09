module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsContinuous
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsApproximation
import PDEFoundation.Measure.LpTendsto
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extending sharp smooth-test bounds to measurable compactly supported tests

Approximation takes place against the sum of the Haar and tested measures. Thus the
reference `Lp` norm and the integral against the tested measure converge together.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The sum of two measures finite on compacts is finite on compacts. -/
theorem finiteOnCompacts_add (ν μ : Measure E) [IsFiniteMeasureOnCompacts ν]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (ν + μ) := by
  constructor
  intro K hK
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩

/-- Compact measurable tests inherit the sharp norm bound from positive smooth tests. -/
theorem abs_integral_le_of_smooth_tests_compact (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hfp : MemLp f p (ν + μ)) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (hfK : Function.support f ⊆ K) :
    |∫ x, f x ∂μ| ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have : IsFiniteMeasureOnCompacts (ν + μ) := finiteOnCompacts_add ν μ
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : ε n ≠ 0 := by
    dsimp [ε]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hex (n : ℕ) := exists_continuous_test_approximation (ν + μ) hpt hfp
    hK hU hKU hfK (hεpos n)
  choose g hgc hgcompact hgU hgn using hex
  have hμsum : μ ≤ ν + μ := Measure.le_add_left le_rfl
  have hνsum : ν.restrict U ≤ ν + μ := Measure.restrict_le_self.trans (Measure.le_add_right le_rfl)
  have herrμ : Tendsto (fun n => eLpNorm (g n - f) p μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεlim
      (Eventually.of_forall fun _ => bot_le) ?_
    exact Eventually.of_forall fun n =>
      (eLpNorm_mono_measure _ hμsum).trans (hgn n)
  have herrν : Tendsto (fun n => eLpNorm (g n - f) p (ν.restrict U))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hεlim
      (Eventually.of_forall fun _ => bot_le) ?_
    exact Eventually.of_forall fun n =>
      (eLpNorm_mono_measure _ hνsum).trans (hgn n)
  have hLpμ : MemLp f p μ := hfp.mono_measure hμsum
  have hL1 := tendsto_eLpNorm_one_of_finite μ hp
    (fun n => (hgc n).aestronglyMeasurable.sub hLpμ.aestronglyMeasurable) herrμ
  have hi : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_L1' f
      (Eventually.of_forall fun n => (hgc n).integrable_of_hasCompactSupport
        (hgcompact n)) hL1
  have hLpν : MemLp f p (ν.restrict U) := hfp.mono_measure hνsum
  have hn := PDE.tendsto_eLpNorm_of_tendsto_sub hp
    (fun n => (hgc n).aestronglyMeasurable) hLpν.aestronglyMeasurable
    hLpν.eLpNorm_ne_top herrν
  have hnr : Tendsto (fun n => (eLpNorm (g n) p (ν.restrict U)).toReal)
      atTop (𝓝 (eLpNorm f p (ν.restrict U)).toReal) :=
    (ENNReal.continuousAt_toReal hLpν.eLpNorm_ne_top).tendsto.comp hn
  exact le_of_tendsto_of_tendsto' hi.abs (tendsto_const_nhds.mul hnr)
    (fun n => abs_integral_le_of_smooth_tests ν μ hU hp hpt hC htest
      (hgc n) (hgcompact n) (hgU n))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Bounded measurable functions supported on a compact set belong to every finite `Lp`. -/
theorem memLp_of_bounded_compact_support (η : Measure E) [IsFiniteMeasureOnCompacts η]
    {f : E → ℝ} (hf : Measurable f) {K : Set E} (hK : IsCompact K)
    (hfK : Function.support f ⊆ K) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (p : ℝ≥0∞) : MemLp f p η := by
  have : IsFiniteMeasure (η.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hfp : MemLp f p (η.restrict K) :=
    MemLp.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  have heq : K.indicator f = f := by
    ext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (Function.notMem_support.mp (fun h => hx (hfK h))).symm
  rw [← heq]
  exact (memLp_indicator_iff_restrict hK.measurableSet).2 hfp

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
