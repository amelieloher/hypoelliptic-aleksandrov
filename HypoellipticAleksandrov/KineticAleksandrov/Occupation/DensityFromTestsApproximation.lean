module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Compact approximation inside the smooth-test region

Multiplication by a fixed cutoff preserves compact interior support and contracts the
approximation error. The approximation measure may be the sum of reference and tested measures.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth compact cutoff equals one on a prescribed compact subset of an open set. -/
theorem exists_test_cutoff {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨δ, hδ, hdouble, χ, hs, h01, h1, h0⟩ := exists_smooth_cutoff hU hK hKU
  have hcompact : IsCompact (cthickening δ K) := hK.cthickening
  have hc : HasCompactSupport χ := HasCompactSupport.intro hcompact h0
  have hsupport : tsupport χ ⊆ cthickening δ K := by
    exact closure_minimal (fun x hx => by
      by_contra hn
      exact hx (h0 x hn)) isClosed_cthickening
  refine ⟨χ, hs, hc, hsupport.trans ?_, h01, h1⟩
  exact (cthickening_mono (by linarith) K).trans hdouble

/-- A compactly supported `Lp` function admits continuous approximants supported inside `U`. -/
theorem exists_continuous_test_approximation (η : Measure E)
    [η.Regular] {p : ℝ≥0∞} (hpt : p ≠ ∞)
    {f : E → ℝ} (hfp : MemLp f p η) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hfK : Function.support f ⊆ K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      eLpNorm (g - f) p η ≤ ε := by
  obtain ⟨χ, hs, hc, hχU, h01, h1⟩ := exists_test_cutoff hK hU hKU
  obtain ⟨a, _hac, han, ha, _hap⟩ :=
    hfp.exists_hasCompactSupport_eLpNorm_sub_le hpt hε
  refine ⟨fun x => χ x * a x, hs.continuous.mul ha, hc.mul_right,
    tsupport_mul_subset_left.trans hχU, ?_⟩
  have heq : (fun x => χ x * a x) - f = fun x => χ x * (a x - f x) := by
    funext x
    by_cases hx : f x = 0
    · simp [hx]
    · have hxK : x ∈ K := hfK hx
      simp [h1 x hxK]
  rw [heq]
  refine (eLpNorm_mono_ae (g := a - f)
    (hs.continuous.aestronglyMeasurable.mul (ha.aestronglyMeasurable.sub
      hfp.aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · change ‖χ x * (a x - f x)‖ ≤ ‖a x - f x‖
    rw [norm_mul, Real.norm_of_nonneg (h01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (h01 x).2
  · simpa only [eLpNorm_sub_comm] using han

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Finite-measure `Lp` convergence, for `p ≥ 1`, implies `L¹` convergence. -/
theorem tendsto_eLpNorm_one_of_finite (μ : Measure E) [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {F : ℕ → E → ℝ} {f : E → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (F n - f) μ)
    (h : Filter.Tendsto (fun n => eLpNorm (F n - f) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n - f) 1 μ) Filter.atTop (nhds 0) := by
  let a := μ univ ^ (1 - 1 / p.toReal)
  have ha : a ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hpReal : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      by_cases hpt : p = ∞
      · simp [hpt]
      · have hpr : 1 ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hpt hp
        have hi : 1 / p.toReal ≤ 1 := by
          exact (div_le_one (by linarith)).2 hpr
        linarith
    · exact measure_ne_top μ univ
  have ht := ENNReal.Tendsto.mul_const h (Or.inr ha)
  rw [zero_mul] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  exact Filter.Eventually.of_forall fun n => by
    simpa [a] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hmeas n)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
