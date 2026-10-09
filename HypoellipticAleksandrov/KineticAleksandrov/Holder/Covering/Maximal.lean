module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.MaximalSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Weak maximal estimate for the kinetic cylinder basis

The estimate is proved by disjoint selection, homogeneous inflation volume, and measure
charging. In particular, no metric-ball density theorem is used for the eccentric basis.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- The union of radius-at-most-one cylinders where E occupies at least the threshold.
The threshold is in ENNReal so the measure calculation stays exact before finite conversions. -/
def maximalCylinderUnion {d : ℕ} (E : Set (KineticPoint d)) (tau : ENNReal) :
    Set (KineticPoint d) :=
  ⋃ z ∈ {z : KineticPoint d × ℝ | 0 < z.2 ∧ z.2 ≤ 1 ∧
    tau * volume (backwardCylinder z.1 z.2) ≤ volume (E ∩ backwardCylinder z.1 z.2)},
    backwardCylinder z.1 z.2

/-- A density-threshold cylinder family satisfies the homogeneous weak measure estimate. -/
theorem cylinder_family_weak_type {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (E : Set (KineticPoint d)) (tau : ENNReal)
    (hdensity : ∀ i ∈ t, tau * volume (backwardCylinder (P i) (r i)) ≤
      volume (E ∩ backwardCylinder (P i) (r i))) :
    tau * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal ((8 : ℝ) ^ (4*d+2)) * volume E := by
  obtain ⟨u, hut, _, _, hcover, hcharge⟩ :=
    exists_disjoint_selection_measure_bounds P r t R hr hR E
  let C := ENNReal.ofReal ((8 : ℝ) ^ (4*d+2))
  calc
    tau * volume (⋃ i ∈ t, backwardCylinder (P i) (r i)) ≤
        tau * ∑' i : u, volume (inflatedCylinder (P i) (r i) 8) :=
      mul_le_mul_right hcover tau
    _ = C * ∑' i : u, tau * volume (backwardCylinder (P i) (r i)) := by
      simp_rw [volume_inflatedCylinder (P _) (hr _ (hut (Subtype.prop _)))]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      exact mul_left_comm _ _ _
    _ ≤ C * ∑' i : u, volume (E ∩ backwardCylinder (P i) (r i)) := by
      apply mul_le_mul_right
      exact ENNReal.tsum_le_tsum fun i => hdensity i (hut i.2)
    _ ≤ C * volume E := mul_le_mul_right hcharge C

/-- The literal kinetic maximal set satisfies a weak (1,1) estimate for indicators. -/
theorem maximalCylinderUnion_weak_type {d : ℕ} (E : Set (KineticPoint d)) (tau : ENNReal) :
    tau * volume (maximalCylinderUnion E tau) ≤
      ENNReal.ofReal ((8 : ℝ) ^ (4*d+2)) * volume E := by
  exact cylinder_family_weak_type Prod.fst Prod.snd
    {z : KineticPoint d × ℝ | 0 < z.2 ∧ z.2 ≤ 1 ∧
      tau * volume (backwardCylinder z.1 z.2) ≤ volume (E ∩ backwardCylinder z.1 z.2)}
    1 (fun _ hz => hz.1) (fun _ hz => hz.2.1) E tau (fun _ hz => hz.2.2)

/-- The kinetic maximal set is open. -/
theorem isOpen_maximalCylinderUnion {d : ℕ} (E : Set (KineticPoint d)) (tau : ENNReal) :
    IsOpen (maximalCylinderUnion E tau) :=
  isOpen_biUnion fun z _ => isOpen_cylinder z.1 z.2

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
