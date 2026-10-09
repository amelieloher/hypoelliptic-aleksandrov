module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # The fixed interior cap in the nearly-full growth argument -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The cap with the manuscript's Euclidean radii and time interval. -/
def cap (d : ℕ) : Set (KineticPoint d) :=
  {P | -(1 / 4 : ℝ) < P.time ∧ P.time < -(1 / 8 : ℝ) ∧
    P.position ∈ PDE.euclideanBall 0 ((8 : ℝ)⁻¹ ^ 3) ∧
    P.velocity ∈ PDE.euclideanBall 0 (1 / 8)}

/-- Closed rectangular envelope of the source cap. -/
def closedCap (d : ℕ) : Set (KineticPoint d) :=
  (KineticPoint.equivProd d) ⁻¹'
    (Icc (-(1 / 4 : ℝ)) (-(1 / 8 : ℝ)) ×ˢ
      (PDE.euclideanClosedBall (0 : PDE.Vec d) ((8 : ℝ)⁻¹ ^ 3) ×ˢ
        PDE.euclideanClosedBall (0 : PDE.Vec d) (1 / 8)))

/-- The closed cap envelope is compact in the physical coordinate topology. -/
theorem isCompact_closedCap (d : ℕ) : IsCompact (closedCap d) := by
  apply (KineticPoint.homeomorphProd d).isCompact_preimage.mpr
  exact (isCompact_Icc.prod
    ((PDE.isCompact_euclideanClosedBall (0 : PDE.Vec d)
      (show 0 ≤ (8 : ℝ)⁻¹ ^ 3 by norm_num)).prod
      (PDE.isCompact_euclideanClosedBall (0 : PDE.Vec d)
        (show 0 ≤ (1 / 8 : ℝ) by norm_num))))

/-- The cap is contained in its closed envelope. -/
theorem cap_subset_closedCap (d : ℕ) : cap d ⊆ closedCap d := by
  intro P hP
  rcases hP with ⟨ht, ht', hx, hv⟩
  exact ⟨⟨ht.le, ht'.le⟩, PDE.euclideanBall_subset_euclideanClosedBall 0 _ hx,
    PDE.euclideanBall_subset_euclideanClosedBall 0 _ hv⟩

/-- Every limit point of the cap remains in its compact closed envelope. -/
theorem closure_cap_subset_closedCap (d : ℕ) : closure (cap d) ⊆ closedCap d :=
  closure_minimal (cap_subset_closedCap d) (isCompact_closedCap d).isClosed

/-- The cap closure is compact. -/
theorem isCompact_closure_cap (d : ℕ) : IsCompact (closure (cap d)) :=
  (isCompact_closedCap d).of_isClosed_subset isClosed_closure
    (closure_cap_subset_closedCap d)

/-- The closed envelope lies strictly inside the unit backward cylinder. -/
theorem closedCap_subset_unitCylinder (d : ℕ) :
    closedCap d ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
  intro P hP
  change P.time ∈ Icc (-(1 / 4 : ℝ)) (-(1 / 8 : ℝ)) ∧
    P.position ∈ PDE.euclideanClosedBall 0 ((8 : ℝ)⁻¹ ^ 3) ∧
    P.velocity ∈ PDE.euclideanClosedBall 0 (1 / 8) at hP
  rcases hP with ⟨⟨ht, ht'⟩, hx, hv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num at *
    linarith
  · norm_num at *
    linarith
  · exact PDE.euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num) hv
  · simpa only [relativePosition, sub_zero, smul_zero, one_pow] using
      PDE.euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num) hx

/-- The source cap is compactly contained in the unit backward cylinder. -/
theorem cap_compact_inside (d : ℕ) :
    IsCompact (closure (cap d)) ∧
      closure (cap d) ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 :=
  ⟨isCompact_closure_cap d,
    (closure_cap_subset_closedCap d).trans (closedCap_subset_unitCylinder d)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
