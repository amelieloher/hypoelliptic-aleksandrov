module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Topology.Separation.Regular

/-!
# Nested compact collars for weak representatives

This module records the topological collar used to localize a relatively
compact open carrier before applying compactly supported weak-jet cutoffs.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

/-- A relatively compact open set inside an open carrier admits a second
relatively compact open collar. -/
theorem exists_open_compact_closure_collar
    {d : Nat} {U V : Set (TimeVelocity d)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVcompact : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ W : Set (TimeVelocity d),
      IsOpen W ∧ IsCompact (closure W) ∧
      closure V ⊆ W ∧ closure W ⊆ U := by
  obtain ⟨L, hLcompact, hLclosed, hVinterior, hLU⟩ :=
    exists_compact_closed_between hVcompact hU hVU
  have hVsubset : V ⊆ interior L := subset_closure.trans hVinterior
  have hW : interior L ∪ V = interior L := union_eq_left.mpr hVsubset
  have hclosure : closure (interior L) ⊆ L :=
    closure_minimal interior_subset hLclosed
  have hWcompact : IsCompact (closure (interior L ∪ V)) := by
    rw [hW]
    exact IsCompact.of_isClosed_subset hLcompact isClosed_closure hclosure
  have hVclosureW : closure V ⊆ interior L ∪ V := by
    rw [hW]
    exact hVinterior
  have hWclosureU : closure (interior L ∪ V) ⊆ U := by
    rw [hW]
    exact hclosure.trans hLU
  exact ⟨interior L ∪ V, isOpen_interior.union hV, hWcompact,
    hVclosureW, hWclosureU⟩

end HypoellipticAleksandrov.Parabolic
