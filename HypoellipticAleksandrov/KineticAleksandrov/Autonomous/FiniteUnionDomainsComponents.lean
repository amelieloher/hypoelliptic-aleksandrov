module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
import Mathlib.Topology.Connected.Basic

/-! # Connected smaller intervals belong to one larger disjoint component -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

/-- An interval included in a finite disjoint interval union lies in one component. -/
theorem Interval.exists_component_containing (I : Interval) (H : FiniteIntervalUnion)
    (hsub : I.carrier ⊆ H.carrier) : ∃ j, I.carrier ⊆ (H.component j).carrier := by
  let v := (I.lo + I.hi) / 2
  have hv : v ∈ I.carrier := by
    change I.lo < v ∧ v < I.hi
    dsimp only [v]
    constructor <;> linarith [I.ordered]
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hv)
  let V : Set ℝ := ⋃ k, ⋃ (_ : k ≠ j), (H.component k).carrier
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_Ioo))
  have hd : Disjoint (H.component j).carrier V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨k, hk, hxk⟩ := mem_iUnion.mp hxV |>.imp fun _ h => mem_iUnion.mp h
    exact Set.disjoint_left.mp (H.disjoint hk.symm) hx hxk
  have hc : I.carrier ⊆ (H.component j).carrier ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsub hx)
    by_cases hkj : k = j
    · exact Or.inl (hkj ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkj, hk⟩⟩)
  exact ⟨j, IsPreconnected.subset_left_of_subset_union isOpen_Ioo hV hd hc
    ⟨v, hv, hj⟩ isPreconnected_Ioo⟩

/-- Every component of a nested finite union lies in a component of the larger union. -/
theorem FiniteIntervalUnion.component_contained (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (i : Fin H1.count) :
    ∃ j, (H1.component i).carrier ⊆ (H2.component j).carrier :=
  (H1.component i).exists_component_containing H2 ((H1.component_subset i).trans hsub)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
