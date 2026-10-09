module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Smooth primitives for the capacity test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A smooth real function has a smooth integral primitive. -/
theorem capacity_primitive_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ x in a..v, f x) := by
  have hd (v : ℝ) : HasDerivAt (fun v => ∫ x in a..v, f x) (f v) v :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable a v)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun v => (hd v).differentiableAt, ?_⟩
  have he : deriv (fun v => ∫ x in a..v, f x) = f := funext fun v => (hd v).deriv
  rw [he]
  exact hf

/-- The cumulative integral of a nonnegative compactly supported function is bounded
by its total integral when its support lies to the right of the starting point. -/
theorem capacity_cumulative_bounds {f : ℝ → ℝ} {a : ℝ}
    (hi : Integrable f volume) (hn : ∀ v, 0 ≤ f v)
    (hs : tsupport f ⊆ Ioi a) (v : ℝ) :
    0 ≤ (∫ x in a..v, f x) ∧ (∫ x in a..v, f x) ≤ ∫ x, f x := by
  by_cases hav : a ≤ v
  · rw [intervalIntegral.integral_of_le hav]
    exact ⟨integral_nonneg (fun x => hn x),
      setIntegral_le_integral hi (Filter.Eventually.of_forall hn)⟩
  · have hva : v ≤ a := (not_le.mp hav).le
    have hz : (∫ x in v..a, f x) = 0 := by
      rw [intervalIntegral.integral_of_le hva]
      apply integral_eq_zero_of_ae
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      exact Filter.Eventually.of_forall fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge hx.2) (hs ht))
    rw [intervalIntegral.integral_symm, hz, neg_zero]
    exact ⟨le_rfl, integral_nonneg hn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
