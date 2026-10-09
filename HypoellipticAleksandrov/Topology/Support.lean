module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support

/-!
# Continuity from localized topological support

This module records a support-local continuity gluing lemma for real-valued
functions on an arbitrary topological space.
-/

@[expose] public section

namespace HypoellipticAleksandrov

/-- The product of two functions continuous on an open set is globally
continuous when the topological support of the first lies in that set. -/
theorem continuous_mul_of_tsupport_subset
    {X : Type*} [TopologicalSpace X] {U : Set X} {b q : X → ℝ}
    (hU : IsOpen U) (hb : ContinuousOn b U) (hbsupp : tsupport b ⊆ U)
    (hq : ContinuousOn q U) :
    Continuous (fun x => b x * q x) := by
  refine (hb.mul hq).continuous_of_tsupport_subset hU ?_
  exact (tsupport_mul_subset_left (f := b) (g := q)).trans hbsupp

/-- A unit-bounded compact cutoff turns locally continuous, locally bounded
data into a globally continuous, compactly supported, globally bounded field. -/
theorem continuous_hasCompactSupport_norm_le_cutoff_mul
    {X : Type*} [TopologicalSpace X] {U : Set X}
    {b q : X → ℝ} {C : ℝ}
    (hU : IsOpen U)
    (hb : ContinuousOn b U)
    (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b ⊆ U)
    (hbunit : ∀ x, ‖b x‖ ≤ 1)
    (hq : ContinuousOn q U)
    (hqbound : ∀ x ∈ tsupport b, ‖q x‖ ≤ C) :
    Continuous (fun x => b x * q x) ∧
      HasCompactSupport (fun x => b x * q x) ∧
      ∀ x, ‖b x * q x‖ ≤ max C 0 := by
  refine ⟨continuous_mul_of_tsupport_subset hU hb hbsupp hq, hbcompact.mul_right, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport b
  · rw [Real.norm_eq_abs, abs_mul]
    calc
      |b x| * |q x| ≤ 1 * C :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using hbunit x)
          (by simpa only [Real.norm_eq_abs] using hqbound x hx)
          (by simpa only [Real.norm_eq_abs] using (norm_nonneg (q x))) zero_le_one
      _ = C := one_mul C
      _ ≤ max C 0 := le_max_left _ _
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp only [zero_mul, norm_zero]
    exact le_max_right _ _

end HypoellipticAleksandrov
