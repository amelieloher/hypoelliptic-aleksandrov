module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Selection
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Basic

/-! # Measure charging for disjoint kinetic selections

The geometric selection simultaneously bounds the covered measure by inflated volumes
and charges the selected intersections to the original set. The homogeneous volume
comparison needed for the weak maximal estimate is a separate dependency.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Disjoint selected cylinders charge their intersections to any set E, while their
inflations cover the original family. No measurability of E is needed for this charging. -/
theorem exists_disjoint_selection_measure_bounds {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R) (E : Set (KineticPoint d)) :
    ∃ u ⊆ t, u.Countable ∧
      u.PairwiseDisjoint (fun i => backwardCylinder (P i) (r i)) ∧
      volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
        ∑' i : u, volume (inflatedCylinder (P i) (r i) 8) ∧
      (∑' i : u, volume (E ∩ backwardCylinder (P i) (r i))) ≤ volume E := by
  obtain ⟨u, hut, hcount, hdisj, hcover⟩ :=
    exists_disjoint_cylinder_selection P r t R hr hR
  refine ⟨u, hut, hcount, hdisj, ?_, ?_⟩
  · exact (measure_mono hcover).trans
      (measure_biUnion_le volume hcount (fun i => inflatedCylinder (P i) (r i) 8))
  · calc
      (∑' i : u, volume (E ∩ backwardCylinder (P i) (r i))) =
          ∑' i : u, (volume.restrict E) (backwardCylinder (P i) (r i)) := by
        apply tsum_congr
        intro i
        rw [Measure.restrict_apply (isOpen_cylinder (P i) (r i)).measurableSet,
          inter_comm]
      _ = (volume.restrict E) (⋃ i ∈ u, backwardCylinder (P i) (r i)) :=
        (measure_biUnion hcount hdisj
          (fun i _ => (isOpen_cylinder (P i) (r i)).measurableSet)).symm
      _ ≤ (volume.restrict E) univ := measure_mono (subset_univ _)
      _ = volume E := Measure.restrict_apply_univ E

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
