module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstruction

/-! # The closed terminal/lateral boundary used for Riesz representation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The closed exit carrier contains the whole past lateral faces and the terminal face.
The actual measure's future-time support is a separate theorem. -/
def stripClosedExit (H : Interval) (T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ Icc H.lo H.hi} ∪
    {p | p.time ≤ T ∧ (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi)}

/-- The full exit carrier is closed in physical kinetic spacetime. -/
theorem isClosed_stripClosedExit (H : Interval) (T : ℝ) : IsClosed (stripClosedExit H T) :=
  ((isClosed_eq continuous_time continuous_const).inter
    (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity))).union
    ((isClosed_le continuous_time continuous_const).inter
      ((isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const).union
        (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const)))

/-- Every prescribed exit point lies on the closed carrier. -/
theorem reconstructionExit_subset_closedExit (H : Interval) (sMinus T : ℝ) :
    reconstructionExit H sMinus T ⊆ stripClosedExit H T := by
  intro p hp
  rcases hp with ht | hv
  · exact Or.inl ht
  · exact Or.inr ⟨hv.2.1.le, hv.2.2⟩

/-- Swapping a native closed slab gives interior or prescribed exit points on any lower strip. -/
theorem reconstruction_closedSlab_mapsTo (H : Interval) {sMinus a T : ℝ}
    (ha : sMinus < a) :
    MapsTo sectionTwoPoint (movingClosedSlab (intervalDomain H) (fun _ => 0) a T)
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T) := by
  intro p hp
  have hv := intervalDomain_closure_bounds H (by
    simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2.2)
  by_cases ht : p.time = T
  · exact Or.inr (Or.inl ⟨ht, hv⟩)
  · have htl : sMinus < p.time := ha.trans_le hp.1
    have htu : p.time < T := lt_of_le_of_ne hp.2.1 ht
    by_cases hl : p.position 0 = H.lo
    · exact Or.inr (Or.inr ⟨htl, htu, Or.inl hl⟩)
    · by_cases hh : p.position 0 = H.hi
      · exact Or.inr (Or.inr ⟨htl, htu, Or.inr hh⟩)
      · exact Or.inl ⟨htl, htu, lt_of_le_of_ne hv.1 (Ne.symm hl), lt_of_le_of_ne hv.2 hh⟩

/-- The native interval frontier consists of exactly the two scalar endpoints. -/
theorem reconstruction_interval_frontier_eq (H : Interval) {v : PDE.Vec 1}
    (hv : v ∈ frontier (intervalDomain H)) : v 0 = H.lo ∨ v 0 = H.hi := by
  have hb := intervalDomain_closure_bounds H (frontier_subset_closure hv)
  change v ∈ closure (intervalDomain H) ∧ v ∉ interior (intervalDomain H) at hv
  have hn : v ∉ interior (intervalDomain H) := hv.2
  rw [(isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)).interior_eq] at hn
  by_cases hl : v 0 = H.lo
  · exact Or.inl hl
  · right
    by_contra hh
    apply hn
    apply PDE.mem_oneDimensionalAxisBox_iff.mpr
    exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hl), lt_of_le_of_ne hb.2 hh⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
