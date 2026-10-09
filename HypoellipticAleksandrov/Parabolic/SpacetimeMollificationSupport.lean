module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

/-!
# Support of spacetime mollification

This module records the closed-thickening support bound for the fixed
spacetime mollification.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

/-- Topological support of a positive-radius mollification lies in the
closed radius thickening of the original topological support. -/
theorem tsupport_spacetimeMollification_subset_cthickening
    {d : ℕ} {f : TimeVelocity d → ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (spacetimeMollification ε f) ⊆
      Metric.cthickening ε (tsupport f) := by
  have hsupp : Function.support (spacetimeMollification ε f) ⊆
      Metric.thickening ε (tsupport f) := by
    intro z hz
    have hzsum := support_convolution_subset
      (ContinuousLinearMap.lsmul ℝ ℝ) hz
    rcases hzsum with ⟨x, hx, y, hy, rfl⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨y, subset_tsupport f hy, ?_⟩
    rw [dist_eq_norm]
    simpa [spacetimeMollifier_support hε] using hx
  exact (closure_mono hsupp).trans
    (Metric.closure_thickening_subset_cthickening ε (tsupport f))

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
