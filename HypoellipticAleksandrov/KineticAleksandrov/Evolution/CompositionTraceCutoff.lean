module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.Tactic.Linarith

/-!
# Smooth compact interior cutoffs

Cutoffs equal one on a prescribed compact subset of an open finite-dimensional state
space. Their entire topological support remains in the open set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Function

/-- A continuous bounded function vanishing outside an open set can be cut off with
arbitrarily small error relative to any continuous positive proper weight. -/
theorem exists_smooth_cutoff_weighted_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (g W : E → ℝ) (hg : Continuous g)
    (hW : Continuous W) (hW1 : ∀ x, 1 ≤ W x)
    (hproper : ∀ R : ℝ, IsCompact {x | W x ≤ R})
    (hzero : ∀ x ∉ U, g x = 0) {C ε : ℝ} (hC : ∀ x, |g x| ≤ C) (hε : 0 < ε) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, |g x - χ x * g x| ≤ ε * W x) := by
  let K : Set E := {x | ε * W x ≤ |g x|}
  have hKclosed : IsClosed K := isClosed_le (continuous_const.mul hW) hg.abs
  have hKcompact : IsCompact K := (hproper (C / ε)).of_isClosed_subset hKclosed
    (fun x hx => (le_div_iff₀ hε).mpr (by
      have hh := (show ε * W x ≤ |g x| from hx).trans (hC x)
      simpa only [mul_comm] using hh))
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hxu
    have hh : ε * W x ≤ 0 := by
      have hk : ε * W x ≤ |g x| := hx
      rw [hzero x hxu, abs_zero] at hk
      exact hk
    have hpos : 0 < ε * W x := mul_pos hε (lt_of_lt_of_le zero_lt_one (hW1 x))
    exact (not_le_of_gt hpos) hh
  obtain ⟨χ, hχ, hc, hs, hr, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen hKcompact hU hKU
  refine ⟨χ, hχ, hc, hs, hr, fun x => ?_⟩
  by_cases hx : x ∈ K
  · rw [hone x hx, one_mul, sub_self, abs_zero]
    exact mul_nonneg hε.le (zero_le_one.trans (hW1 x))
  · have herr : |g x| ≤ ε * W x := (not_le.mp hx).le
    have hfactor : 0 ≤ 1 - χ x := sub_nonneg.mpr (hr x).2
    calc
      |g x - χ x * g x| = |(1 - χ x) * g x| := by congr 1; ring
      _ = (1 - χ x) * |g x| := by rw [abs_mul, abs_of_nonneg hfactor]
      _ ≤ 1 * |g x| := mul_le_mul_of_nonneg_right
        (by linarith only [(hr x).1]) (abs_nonneg _)
      _ ≤ ε * W x := by simpa only [one_mul] using herr

end HypoellipticAleksandrov.KineticAleksandrov
