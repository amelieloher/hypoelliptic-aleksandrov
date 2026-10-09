module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicInkSpotsBridge
public import HypoellipticAleksandrov.Measure.ParabolicDyadicOpenCover
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyGeometry

/-!
# Dyadic forward boxes for parabolic Morrey geometry

This module exposes the open dyadic cells as the literal forward
coordinate boxes used by the Morrey layer.  It deliberately does not identify
the half-open partition cells with these boxes.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The existing dyadic source-box data is literally the forward box used by
the physical Morrey projection. -/
theorem parabolicDyadicOpenCell_eq_parabolicBox
    {d n : Nat} (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index =
      parabolicBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  change parabolicDyadicOpenCell index =
    inkSpotsSourceBox (parabolicDyadicSourceBox index)
  exact (inkSpotsSourceBox_parabolicDyadicSourceBox index).symm

/-- One simultaneous dyadic refinement halves the forward-box radius. -/
theorem parabolicDyadicSourceBox_radius_childIndex
    {d n : Nat} (index : ParabolicDyadicIndex d n)
    (child : ParabolicDyadicChild d) :
    (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius =
      (parabolicDyadicSourceBox index).radius / 2 := by
  change ((2 : Real) ^ (n + 1))⁻¹ = ((2 : Real) ^ n)⁻¹ / 2
  rw [pow_succ]
  field_simp

/-- The corresponding child forward box is contained in its parent forward
box, in the orientation expected by normalized restriction. -/
theorem parabolicDyadicForwardBox_child_subset
    {d n : Nat} (index : ParabolicDyadicIndex d n)
    (child : ParabolicDyadicChild d) :
    parabolicBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).center ⊆
      parabolicBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  rw [← parabolicDyadicOpenCell_eq_parabolicBox
        (parabolicDyadicChildIndex index child),
    ← parabolicDyadicOpenCell_eq_parabolicBox index]
  exact parabolicDyadicOpenCell_child_subset index child

/-- Any addressed descendant gives the literal forward-box inclusion needed
by the nested-projection API. -/
theorem parabolicDyadicForwardBox_subset_of_addressPrefix
    {d : Nat} {a b : ParabolicDyadicAddress d}
    (hab : parabolicDyadicAddressPrefix a b) :
    parabolicBox 1
        (parabolicDyadicSourceBox b.2).radius
        (parabolicDyadicSourceBox b.2).baseTime
        (parabolicDyadicSourceBox b.2).center ⊆
      parabolicBox 1
        (parabolicDyadicSourceBox a.2).radius
        (parabolicDyadicSourceBox a.2).baseTime
        (parabolicDyadicSourceBox a.2).center := by
  rw [← parabolicDyadicOpenCell_eq_parabolicBox b.2,
    ← parabolicDyadicOpenCell_eq_parabolicBox a.2]
  exact parabolicDyadicOpenCell_subset_of_addressPrefix hab

/-- A single dyadic forward box has parabolic-coordinate diameter at most
twice its radius. -/
theorem parabolicCoordinateDist_le_two_mul_parabolicDyadicSourceBox_radius
    {d n : Nat} (index : ParabolicDyadicIndex d n)
    {z w : TimeVelocity d}
    (hz : z ∈ parabolicBox 1
      (parabolicDyadicSourceBox index).radius
      (parabolicDyadicSourceBox index).baseTime
      (parabolicDyadicSourceBox index).center)
    (hw : w ∈ parabolicBox 1
      (parabolicDyadicSourceBox index).radius
      (parabolicDyadicSourceBox index).baseTime
      (parabolicDyadicSourceBox index).center) :
    parabolicCoordinateDist z w ≤
      2 * (parabolicDyadicSourceBox index).radius := by
  let q := parabolicDyadicSourceBox index
  have hqRadius : 0 < q.radius := parabolicDyadicSourceBox_radius_pos index
  have hzBox : z.1 > q.baseTime ∧ z.1 < q.baseTime + q.radius ^ 2 ∧
      z.2 ∈ velocityCube q.center q.radius := by
    simpa only [q, one_mul] using (mem_parabolicBox_iff.mp hz)
  have hwBox : w.1 > q.baseTime ∧ w.1 < q.baseTime + q.radius ^ 2 ∧
      w.2 ∈ velocityCube q.center q.radius := by
    simpa only [q, one_mul] using (mem_parabolicBox_iff.mp hw)
  have htimeAbs : |z.1 - w.1| ≤ q.radius ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [hzBox.1, hzBox.2.1, hwBox.1, hwBox.2.1]
  have htime : Real.sqrt |z.1 - w.1| ≤ q.radius := by
    rw [Real.sqrt_le_iff]
    exact ⟨hqRadius.le, htimeAbs⟩
  have hvelocity : ‖z.2 - w.2‖ ≤ 2 * q.radius := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro coordinate
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_le]
    have hzCoordinate := abs_lt.mp ((mem_velocityCube_iff.mp hzBox.2.2) coordinate)
    have hwCoordinate := abs_lt.mp ((mem_velocityCube_iff.mp hwBox.2.2) coordinate)
    constructor <;> linarith [hzCoordinate.1, hzCoordinate.2,
      hwCoordinate.1, hwCoordinate.2]
  unfold parabolicCoordinateDist
  apply max_le
  · linarith
  · exact hvelocity

/-- The dyadic forward-box diameter scale tends to zero. -/
theorem tendsto_two_mul_parabolicDyadicSourceBox_radius_atTop :
    Tendsto (fun n : Nat => 2 * ((2 : Real) ^ n)⁻¹) atTop (nhds 0) := by
  have heq : parabolicDyadicVelocityWidth =
      (fun n : Nat => 2 * ((2 : Real) ^ n)⁻¹) := by
    funext n
    exact rfl
  rw [← heq]
  exact tendsto_parabolicDyadicVelocityWidth_atTop

end

end HypoellipticAleksandrov.Parabolic
