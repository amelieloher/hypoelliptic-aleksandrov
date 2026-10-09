module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCollar
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Compact-open bounds for spatial difference quotients

This module obtains a uniform signed spatial difference-quotient bound on a
compact time--velocity carrier from continuous differentiability on an open
neighborhood.  The quotient remains totalized at a zero increment.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Convex

private theorem segment_subset_cthickening_of_spatialShift
    {d : ℕ} {S : Set (TimeVelocity d)} {δ h : ℝ} {k : Fin d}
    {z : TimeVelocity d} (hz : z ∈ S) (hh : |h| ≤ δ) :
    [z -[ℝ] spatialShift k h z] ⊆ Metric.cthickening δ S := by
  intro w hw
  apply Metric.mem_cthickening_of_dist_le w z δ S hz
  calc
    dist w z = ‖w - z‖ := dist_eq_norm _ _
    _ ≤ ‖spatialShift k h z - z‖ := norm_sub_le_of_mem_segment hw
    _ = dist (spatialShift k h z) z := (dist_eq_norm _ _).symm
    _ = |h| := dist_spatialShift k h z
    _ ≤ δ := hh

private theorem abs_spatialDifferenceQuotient_le_of_fderiv_bound
    {d : ℕ} {S U : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    {δ C h : ℝ} {k : Fin d} {z : TimeVelocity d}
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U)
    (hδU : Metric.cthickening δ S ⊆ U)
    (hC : ∀ w ∈ Metric.cthickening δ S, ‖fderiv ℝ f w‖ ≤ C)
    (hCnonneg : 0 ≤ C)
    (hh : |h| ≤ δ) (hz : z ∈ S) :
    |spatialDifferenceQuotient k h f z| ≤ C := by
  by_cases hhzero : h = 0
  · subst h
    simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
      spatialShift_zero, id_eq, sub_self, zero_div, abs_zero]
    exact hCnonneg
  · have hsegment : [z -[ℝ] spatialShift k h z] ⊆ Metric.cthickening δ S :=
      segment_subset_cthickening_of_spatialShift hz hh
    have hsegmentU : [z -[ℝ] spatialShift k h z] ⊆ U := hsegment.trans hδU
    have hdifferentiable : ∀ w ∈ [z -[ℝ] spatialShift k h z],
        DifferentiableAt ℝ f w := by
      intro w hw
      exact (hf.contDiffAt (hU.mem_nhds (hsegmentU hw))).differentiableAt_one
    have hbound : ∀ w ∈ [z -[ℝ] spatialShift k h z], ‖fderiv ℝ f w‖ ≤ C := by
      intro w hw
      exact hC w (hsegment hw)
    have hdiff : ‖f (spatialShift k h z) - f z‖ ≤
        C * ‖spatialShift k h z - z‖ :=
      (convex_segment z (spatialShift k h z)).norm_image_sub_le_of_norm_fderiv_le
        hdifferentiable hbound (left_mem_segment ℝ z (spatialShift k h z))
        (right_mem_segment ℝ z (spatialShift k h z))
    have hdiff_abs : |f (spatialShift k h z) - f z| ≤ C * |h| := by
      calc
        |f (spatialShift k h z) - f z| = ‖f (spatialShift k h z) - f z‖ :=
          by rw [Real.norm_eq_abs]
        _ ≤ C * ‖spatialShift k h z - z‖ := hdiff
        _ = C * |h| := by
          rw [← dist_eq_norm, dist_spatialShift]
    rw [spatialDifferenceQuotient_apply, spatialTranslate_apply, abs_div]
    calc
      |f (spatialShift k h z) - f z| / |h| ≤ (C * |h|) / |h| :=
        div_le_div_of_nonneg_right hdiff_abs (abs_nonneg h)
      _ = C := mul_div_cancel_right₀ C (abs_ne_zero.mpr hhzero)

/-- A scalar field which is continuously differentiable on an open neighborhood
has uniformly bounded signed spatial difference quotients on a compact carrier. -/
theorem IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one
    {d : ℕ} {S U : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      Metric.cthickening δ S ⊆ U ∧
      (∀ z ∈ Metric.cthickening δ S, ‖fderiv ℝ f z‖ ≤ C) ∧
      (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Set.MapsTo (spatialShift k h) S U) ∧
      (∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialDifferenceQuotient k h f z| ≤ C) := by
  obtain ⟨δ, hδ, hδU, hshift⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hS hU hSU
  have hcompact : IsCompact (Metric.cthickening δ S) := hS.cthickening
  have hcontinuous : ContinuousOn (fderiv ℝ f) (Metric.cthickening δ S) :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hδU
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn hcontinuous
  refine ⟨δ, max C₀ 0, hδ, le_max_right _ _, hδU, ?_, hshift, ?_⟩
  · intro z hz
    exact (hC₀ z hz).trans (le_max_left _ _)
  · intro k h z hh hz
    exact abs_spatialDifferenceQuotient_le_of_fderiv_bound hU hf hδU
      (fun w hw => (hC₀ w hw).trans (le_max_left _ _)) (le_max_right _ _) hh hz

end HypoellipticAleksandrov.Parabolic
