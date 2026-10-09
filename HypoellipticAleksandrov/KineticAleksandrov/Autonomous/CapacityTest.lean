module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityPrimitive
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The convex velocity test for strip capacity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A smooth convex test with second derivative twice a compact interval majorant. -/
theorem exists_capacity_test (E : Interval) :
    ∃ chi Phi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) ∧ ContDiff ℝ (⊤ : ℕ∞) Phi ∧
      (∀ v, deriv (deriv Phi) v = 2 * chi v) ∧
      (∀ v, |deriv Phi v| ≤ 2 * (E.hi - E.lo)) := by
  obtain ⟨chi, hs, hc, hsup, hn, h1, hm⟩ := exists_capacity_cutoff E
  let a := E.lo - (E.hi - E.lo) / 2
  let F : ℝ → ℝ := fun v => 2 * (∫ x in a..v, chi x) - ∫ x, chi x
  let Phi : ℝ → ℝ := fun v => ∫ x in 0..v, F x
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_const.mul (capacity_primitive_smooth hs a)).sub contDiff_const
  have hdF (v : ℝ) : HasDerivAt F (2 * chi v) v := by
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hs.continuous.intervalIntegrable a v)
      hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt
    exact (hd.const_mul 2).sub_const _
  have hdPhi (v : ℝ) : HasDerivAt Phi (F v) v :=
    intervalIntegral.integral_hasDerivAt_right (hF.continuous.intervalIntegrable 0 v)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
  have he : deriv Phi = F := funext fun v => (hdPhi v).deriv
  refine ⟨chi, Phi, hs, hc, hn, h1, hm, capacity_primitive_smooth hF 0, ?_, ?_⟩
  · intro v
    rw [he]
    exact (hdF v).deriv
  · intro v
    rw [he]
    have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
    have hsupport : tsupport chi ⊆ Ioi a := fun x hx => (hsup hx).1
    obtain ⟨hlo, hhi⟩ := capacity_cumulative_bounds hi (fun x => (hn x).1) hsupport v
    have ht : 0 ≤ ∫ x, chi x := integral_nonneg (fun x => (hn x).1)
    dsimp only [F]
    apply abs_le.mpr
    constructor <;> linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
