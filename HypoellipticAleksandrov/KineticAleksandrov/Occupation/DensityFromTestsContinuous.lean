module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Passing sharp positive smooth-test bounds to continuous tests

The reference measure is Haar measure restricted to the open test region. The tested
measure is finite. Compact supports stay strictly inside that region.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Positive smooth-test bounds extend sharply to continuous compactly supported tests. -/
theorem integral_le_of_smooth_tests (ν μ : Measure E) [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have hfp : MemLp f p (ν.restrict U) := hf.memLp_of_hasCompactSupport hfc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  obtain ⟨g, hgs, hgc, hgU, hg0, hfg, hgn⟩ :=
    exists_smooth_majorant_toReal_le ν hU hfc hfs hf.continuousOn
      (fun x _ => hf0 x) (Filter.Eventually.of_forall fun _ => le_rfl)
      hp hpt hfp hδ
  have hfg' : ∀ x, f x ≤ g x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hfg x hx
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact hg0 x
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ :=
      integral_mono (hf.integrable_of_hasCompactSupport hfc)
        (hgs.continuous.integrable_of_hasCompactSupport hgc) hfg'
    _ ≤ C * (eLpNorm g p (ν.restrict U)).toReal := htest g hgs hgc hgU hg0
    _ ≤ C * ((eLpNorm f p (ν.restrict U)).toReal + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hgn hC
    _ ≤ C * (eLpNorm f p (ν.restrict U)).toReal + ε := by
      have hmul : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
      nlinarith

/-- Positive smooth-test bounds control the absolute integral of signed continuous tests. -/
theorem abs_integral_le_of_smooth_tests (ν μ : Measure E) [ν.IsAddHaarMeasure]
    [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * (eLpNorm f p (ν.restrict U)).toReal)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) :
    |∫ x, f x ∂μ| ≤ C * (eLpNorm f p (ν.restrict U)).toReal := by
  have ha : Continuous (fun x => |f x|) := hf.abs
  have hac : HasCompactSupport (fun x => |f x|) := hfc.norm
  have has : tsupport (fun x => |f x|) ⊆ U := by
    exact (closure_mono (fun x hx => by
      exact fun hz => hx (by simp [hz]))).trans hfs
  have hb := integral_le_of_smooth_tests ν μ hU hp hpt hC htest
    ha hac has (fun x => abs_nonneg (f x))
  have hn : eLpNorm (fun x => |f x|) p (ν.restrict U) =
      eLpNorm f p (ν.restrict U) := by
    simpa only [← Real.norm_eq_abs] using eLpNorm_norm f hf.aestronglyMeasurable
  rw [hn] at hb
  have hi : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
  exact hi.trans hb

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
