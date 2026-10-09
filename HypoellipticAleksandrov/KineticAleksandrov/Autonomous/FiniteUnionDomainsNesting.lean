module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBoundary

/-! # Internal velocity faces and the exact terminal/lateral boundary split -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The internal restart boundary uses strict physical time and the larger open velocity set. -/
def finiteUnionInternalExit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧
    p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier}

/-- The internal restart boundary is part of the smaller strip's prescribed exit. -/
theorem finiteUnionInternalExit_subset_exit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    finiteUnionInternalExit H1 H2 sMinus T ⊆ finiteUnionExitSet H1 sMinus T :=
  fun _ hp => Or.inr ⟨hp.1, hp.2.1, hp.2.2.1⟩

/-- The smaller exit is exactly the outer exit part plus the internal restart part. -/
theorem finiteUnionExitSet_nested_split (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ) :
    finiteUnionExitSet H1 sMinus T =
      (finiteUnionExitSet H1 sMinus T ∩ finiteUnionExitSet H2 sMinus T) ∪
        finiteUnionInternalExit H1 H2 sMinus T := by
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · exact Or.inl ⟨Or.inl hp, Or.inl ⟨hp.1, closure_mono hsub hp.2⟩⟩
    · by_cases hv : p.velocity 0 ∈ H2.carrier
      · exact Or.inr ⟨hp.1, hp.2.1, hp.2.2, hv⟩
      · refine Or.inl ⟨Or.inr hp, Or.inr ⟨hp.1, hp.2.1, ?_⟩⟩
        rw [frontier, H2.isOpen_carrier.interior_eq]
        exact ⟨closure_mono hsub (frontier_subset_closure hp.2.2), hv⟩
  · rintro (hp | hp)
    · exact hp.1
    · exact finiteUnionInternalExit_subset_exit H1 H2 sMinus T hp

/-- Outer prescribed exits and internal restart exits are disjoint. -/
theorem finiteUnionExitSet_disjoint_internal (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    Disjoint (finiteUnionExitSet H2 sMinus T) (finiteUnionInternalExit H1 H2 sMinus T) := by
  apply Set.disjoint_left.mpr
  intro p hp hs
  rcases hp with hp | hp
  · exact (ne_of_lt hs.2.1) hp.1
  · exact Set.disjoint_left.mp
      (disjoint_frontier_iff_isOpen.mpr H2.isOpen_carrier) hp.2.2 hs.2.2.2

/-- The internal restart set is Borel in physical coordinates. -/
theorem measurableSet_finiteUnionInternalExit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    MeasurableSet (finiteUnionInternalExit H1 H2 sMinus T) := by
  unfold finiteUnionInternalExit
  convert ((isOpen_lt continuous_const continuous_time).measurableSet.inter
    (isOpen_lt continuous_time continuous_const).measurableSet).inter
    ((isClosed_frontier.measurableSet.inter H2.isOpen_carrier.measurableSet).preimage
      (((continuous_apply 0).comp continuous_velocity).measurable)) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.comp_apply]
  tauto

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
